package ru.mylogininya

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import java.util.BitSet
import kotlin.io.path.Path
import kotlin.io.path.bufferedReader
import kotlin.io.path.div
import kotlin.io.path.listDirectoryEntries
import kotlin.streams.asSequence

class PointsToAdapterSingleton private constructor(val methodName: String, val depsWithCur: Set<String>) {
    companion object {
        val MAX_ACCESSORS: Int = 5 //5
        private val aliasIdToAlias = mutableListOf<Alias>()
        private val aliasToId: Object2IntOpenHashMap<Alias> = Object2IntOpenHashMap<Alias>().also {
            it.defaultReturnValue(-1)
        }

        private fun getAliasId(alias: Alias): Int {
            val currentId = aliasToId.getInt(alias)
            if (currentId != -1) return currentId

            val id = aliasIdToAlias.size
            aliasToId.put(alias, id)
            aliasIdToAlias.add(alias)
            return id
        }

        val methodList = mutableListOf<Pair<String, Set<String>>>()
        const val homeDirectory = "/home/nikita/processStdlibMethods/taint_in_graph_no_field/graphs"

        private val currentF2fEdgesMap = Int2ObjectOpenHashMap<BitSet>()
        private val currentF2fEdgesMapIdsTo = Int2ObjectOpenHashMap<Int>()
        private val currentF2fEdgesMapIdsFrom = Int2ObjectOpenHashMap<Int>()
        private val currentF2fEdgesMapIdsFromVar = Int2ObjectOpenHashMap<Int>()
        private var currentF2fEdgesMapNum = 0

        val currentZ2FEdges = mutableSetOf<Z2FEdge>()
        val defaultEdges = mutableListOf<F2FEdge>()
        private val fIndToAccessor: MutableMap<Int, String> = mutableMapOf()
        var ptis: List<Pair<Int, PointsToInstance?>>? = null
        var pairList: Int2ObjectOpenHashMap<BitSet>? = null
        var graphList: List<Pair<List<Int>, List<String>>>? = null
        val loadStoreIncidentVs = BitSet()
        val epVertices = BitSet()

        init {
            val countDirEntries = Path(homeDirectory).listDirectoryEntries().count()
            var dirId = 0
            val pts = mutableListOf<Pair<Int, PointsToInstance?>>()
            val prList = mutableListOf<Pair<Int, Int>>()
            val gList = mutableListOf<Pair<List<Int>, List<String>>>()
            Path(homeDirectory).listDirectoryEntries().forEach { projectDirectory ->
                (projectDirectory / "full_methods_list.txt").bufferedReader().forEachLine { line ->
                    val (m, ms) = line.split("@@@")
                    val deps = if (ms.isEmpty()) listOf() else ms.split("@@")
                    methodList.add(Pair(m, (deps + m).toSet()))
                }
                (projectDirectory / "description.txt").bufferedReader().forEachLine { line ->
                    val items = line.split("@@")
                    val pti = when (items[0]) {
                        "this" -> items[1].let { PointsToInstance.This(it, true) }
                        "arg" -> items[1].let { PointsToInstance.Argument(it, items[2].toInt(), true) }
                        else -> throw IllegalArgumentException("Unknown alias base")
                    }
                    val alias = Alias(pti as AliasBase, listOf())
                    defaultEdges.add(F2FEdge(alias, alias))
                }
                (projectDirectory / "field_mappings.txt").bufferedReader().forEachLine { line ->
                    val (num, rest) = line.split("@@")
                    val number = num.toInt() * countDirEntries + dirId
                    fIndToAccessor[number] = if (rest == "PtArrayElementField") {
                        "[*]"
                    } else {
                        val declaration = rest.split("field=")[1].removeSuffix(")")
                        val (_, fieldName) = declaration.split("#")
                        fieldName
                    }
                }
                Path(homeDirectory).listDirectoryEntries().forEach { projectDirectory ->
                    (projectDirectory / "vertex_mappings.txt").bufferedReader().forEachLine { line ->
                        val items = line.split("@@")
                        val id = items[0].toInt() * countDirEntries + dirId
                        val pti = when (items[1]) {
                            "this" -> PointsToInstance.This(items[2])
                            "local" -> PointsToInstance.LocalVar(items[2], items[6].toInt())
                            "temp" -> PointsToInstance.Rubbish(id, items[4])
                            "arg" -> PointsToInstance.Argument(items[2], items[3].toInt())
                            "return" -> PointsToInstance.ReturnValue(items[2])
                            "staticcontext" -> PointsToInstance.Rubbish(id, isOkAlways = true)
                            "staticalloc" -> PointsToInstance.Rubbish(id)
                            "unknown" -> PointsToInstance.Unknown(items[2], items[3])
                            "alloc" -> PointsToInstance.Rubbish(id)
                            else -> null
                        }
                        pts.add(id to pti)
                    }
                }
                (projectDirectory / "results.txt").bufferedReader().forEachLine { line ->
                    val (var1, var2) = line.split(" ", "\t").map { it.toInt() * countDirEntries + dirId }
                    prList.add(var1 to var2)
                }
                (projectDirectory / "slx_result.txt.g").bufferedReader().forEachLine { line ->
                    val items = line.split(" ", "\t")
                    if (items[2] == "entrypoint") {
                        epVertices.set(items[0].toInt() * countDirEntries + dirId)
                    } else if (items[2] == "load_i" || items[2] == "store_i") {
                        gList.add(listOf(items[0], items[1], items[3]).map { it.toInt() * countDirEntries + dirId }
                            .toList() to items)
                        loadStoreIncidentVs.set(gList.last().first[0])
                        loadStoreIncidentVs.set(gList.last().first[1])
                    }
                }
                dirId += 1
            }

            val indexedPairList = Int2ObjectOpenHashMap<BitSet>()
            for ((v1, v2) in prList) {
                var set = indexedPairList.get(v1)
                if (set == null) {
                    set = BitSet().also { indexedPairList.put(v1, it) }
                }
                set.set(v2)
            }

            pairList = indexedPairList
            graphList = gList
            ptis = pts
        }

        fun findEdges(): Pair<List<F2FEdge>, List<Z2FEdge>> {
            var methodId = 1 /////
            for ((method, depsWithCur) in methodList) {
                //if (methodId % 10 == 1) {
                println("$methodId) $method")
                //}
                PointsToAdapterSingleton(method, depsWithCur).findEdges(currentZ2FEdges)
                methodId += 1 /////
            }

            val currentF2fEdges = mutableListOf<F2FEdge>()

            for ((fromAliasId, toAliasSet) in currentF2fEdgesMap) {
                toAliasSet.forEach { toAliasId ->
                    val fromAlias = aliasIdToAlias[fromAliasId]
                    val toAlias = aliasIdToAlias[toAliasId]
                    currentF2fEdges.add(F2FEdge(fromAlias, toAlias))
                }
            }

            currentF2fEdges.addAll(defaultEdges)
            val fs = currentF2fEdges.filter {
                val from = it.from.base
                when (from) {
                    is PointsToInstance.Argument -> from.isEntryPoint
                    is PointsToInstance.ReturnValue -> from.isEntryPoint
                    is PointsToInstance.This -> from.isEntryPoint
                    else -> throw IllegalArgumentException("Unsupported alias base")
                }
            }.toList()
            val zs = currentZ2FEdges.filter {
                val to = it.to.base
                when (to) {
                    is PointsToInstance.Argument -> to.isEntryPoint
                    is PointsToInstance.ReturnValue -> to.isEntryPoint
                    is PointsToInstance.This -> to.isEntryPoint
                    else -> throw IllegalArgumentException("Unsupported alias base")
                }
            }.toList()
            return fs to zs
        }
    }

    sealed interface AliasBase {
        fun getMethodName(): String

        fun getMethodUnifiedName(): String {
            val name = getMethodName()
            if (!(this is PointsToInstance.This || this is PointsToInstance.Argument || this is PointsToInstance.ReturnValue)) {
                throw IllegalStateException("must not be this, arg, rv")
            }
            if (name.contains("<") && !name.contains("<init>")) {
                throw IllegalStateException("must not contain <")
            }
            if (name.contains("(id:")) {
                throw IllegalStateException("must not contain id")
            }
            if (name.contains(", ")) {
                throw IllegalStateException("must not contain ,wsp")
            }
            val (mName, args) = name.split("(", limit = 2)
            val methodName = "$mName(${args.replace("$", ".")}"
            return methodName.replace("#", "::")
        }
    }

    sealed interface PointsToInstance {
        fun getMethodName(): String
        fun isOkWithMethod(m: String, ms: Set<String>): Boolean = getMethodName() == m

        data class Rubbish(val u: Int, val methodOrEmpty: String = "", val isOkAlways: Boolean = false) :
            PointsToInstance, AliasBase {
            override fun getMethodName(): String = methodOrEmpty

            override fun isOkWithMethod(m: String, ms: Set<String>): Boolean = isOkAlways || methodOrEmpty == m
        }

        data class This(val method: String, val isEntryPoint: Boolean = false) : PointsToInstance, AliasBase {
            override fun toString(): String = "this"
            override fun getMethodName(): String = method
            override fun isOkWithMethod(m: String, ms: Set<String>): Boolean = ms.contains(method)
        }

        data class LocalVar(val method: String, val index: Int) : PointsToInstance, AliasBase {
            override fun getMethodName(): String = method
        }

        data class Argument(val method: String, val index: Int, val isEntryPoint: Boolean = false) : PointsToInstance,
            AliasBase {
            override fun toString(): String = "arg($index)"
            override fun getMethodName(): String = method
            override fun isOkWithMethod(m: String, ms: Set<String>): Boolean = ms.contains(method)
        }

        data class ReturnValue(val method: String, val isEntryPoint: Boolean = false) : PointsToInstance, AliasBase {
            override fun toString(): String = "return"
            override fun getMethodName(): String = method
            override fun isOkWithMethod(m: String, ms: Set<String>): Boolean = ms.contains(method)
        }

        data class Unknown(val stdLibMethod: String, val method: String) : PointsToInstance, AliasBase {
            override fun getMethodName(): String = method
        }
    }

    private fun toEntryPoint(pti: PointsToInstance): PointsToInstance =
        when (pti) {
            is PointsToInstance.Argument -> PointsToInstance.Argument(pti.method, pti.index, true)
            is PointsToInstance.ReturnValue -> PointsToInstance.ReturnValue(pti.method, true)
            is PointsToInstance.This -> PointsToInstance.This(pti.method, true)
            else -> pti
        }

    data class Alias(val base: AliasBase, val accessors: List<String>) {
        private val result = 31 * base.hashCode() + accessors.hashCode()

        fun withNewAccessor(accessor: String): Alias {
            if (accessors.size >= MAX_ACCESSORS) {
                return this
            }
            return Alias(base, accessors + accessor)
        }

        fun withNewAccessors(accessorList: List<String>): Alias {
            if (accessors.size >= MAX_ACCESSORS || accessorList.isEmpty()) {
                return this
            }
            return Alias(base, accessors + accessorList.take(MAX_ACCESSORS - accessors.size))
        }

        fun readAccessors(acc: String): Alias? {
            if (accessors.isEmpty() || accessors.first() != acc) {
                return null
            }
            return Alias(base, accessors.drop(1))
        }

        override fun toString(): String = (listOf("$base") + accessors).joinToString(".")

        fun printWithMethod(): String = base.getMethodUnifiedName() + ":" + this.toString()

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false
            other as Alias
            if (result != other.result) return false
            if (base != other.base) return false
            if (accessors != other.accessors) return false
            return true
        }

        override fun hashCode(): Int {
            return result
        }
    }

    private val varToAliasesVarsMap = Int2ObjectOpenHashMap<BitSet>()
    private val indToEntity = Int2ObjectOpenHashMap<PointsToInstance>()
    private val entityToInd = Object2IntOpenHashMap<PointsToInstance>().also {
        it.defaultReturnValue(-1)
    }

    private val storesAndLoads = Int2ObjectOpenHashMap<Int2ObjectOpenHashMap<MutableSet<String>>>()
    private val stores = Int2ObjectOpenHashMap<Int2ObjectOpenHashMap<MutableSet<String>>>()

    //private val loads = Int2ObjectOpenHashMap<Int2ObjectOpenHashMap<MutableSet<String>>>()
    private val varIndToSetOfAliases = Int2ObjectOpenHashMap<BitSet>()

    //private val varIndToLoadSetOfAliases: MutableMap<Int, BitSet> = mutableMapOf()
    private val unknownToIds: MutableMap<String, BitSet> = mutableMapOf()


    val okVars = BitSet()

    private val multiStoresAndLoads = Int2ObjectOpenHashMap<Int2ObjectOpenHashMap<MutableSet<List<String>>>>()
    private val multiStores = Int2ObjectOpenHashMap<Int2ObjectOpenHashMap<MutableSet<List<String>>>>()

    //val multiLoads = Int2ObjectOpenHashMap<Int2ObjectOpenHashMap<MutableSet<List<String>>>>()
    init {
        loadPointsToInformation()
    }

    private fun addAliasesUsingFields() {
        println(
            "Summary ribs: ${
                multiStoresAndLoads.map { i -> i.value.map { j -> j.value.size }.sum() }.sum()
            } Graph: ${storesAndLoads.map { i -> i.value.map { j -> j.value.size }.sum() }.sum()}"
        ) ////
//        if (true) {
//            val se = storesAndLoads.flatMap { a ->
//                a.value.flatMap { b->
//                    b.value.map { str ->
//                        Triple(indToEntity[a.key], indToEntity[b.key], str)
//                    }
//                }
//            }.toList()
//            val sms = multiStoresAndLoads.flatMap { a ->
//                a.value.flatMap { b->
//                    b.value.map { str ->
//                        Triple(indToEntity[a.key], indToEntity[b.key], str)
//                    }
//                }
//            }.toList()
//            val ss = currentF2fEdgesMap.flatMap { f ->
//                f.value.stream().asSequence().map { t ->
//                    Pair(aliasIdToAlias[f.key], aliasIdToAlias[t])
//                }
//            }.toList()
//            print("OK")
//        } ////

        val queue = IntArrayList()
        val inQueue = BitSet()
        for ((vI, als) in varIndToSetOfAliases) {
            if (als.cardinality() > 0) {
                queue.add(vI)
                inQueue.set(vI)
            }
        }
        while (queue.isNotEmpty()) {
//            if (methodName == "org.apache.logging.log4j.core.filter.StringMatchFilter#filter(org.apache.logging.log4j.core.Logger,org.apache.logging.log4j.Level,org.apache.logging.log4j.Marker,java.lang.String,java.lang.Object,java.lang.Object)") {
//                println("q sz: ${queue.size}") ////
//            }
            val aInd = queue.removeLast()
            inQueue.clear(aInd)
            val aSet = varIndToSetOfAliases[aInd]!!.clone() as BitSet
            processGraphRibs(aInd, aSet, inQueue, queue)
            processSummaryRibs(aInd, aSet, inQueue, queue)
        }
    }

    private fun processSummaryRibs(
        aInd: Int,
        aSet: BitSet,
        inQueue: BitSet,
        queue: IntArrayList
    ) {
        val bInd2Accss = multiStoresAndLoads[aInd]
        if (bInd2Accss != null) {
            //                if (methodName == "org.apache.logging.log4j.core.filter.StringMatchFilter#filter(org.apache.logging.log4j.core.Logger,org.apache.logging.log4j.Level,org.apache.logging.log4j.Marker,java.lang.String,java.lang.Object,java.lang.Object)") {
            //                    val suspected = aSet.stream().asSequence().map { aliasIdToAlias[it] }.toList()
            //                    println("aSyns sz: ${aSet.cardinality()}") ////
            //                }
            val iter = bInd2Accss.int2ObjectEntrySet().fastIterator()
            while (iter.hasNext()) {
                val entry = iter.next()
                val bInd = entry.intKey
                val accss = entry.value
                aSet.forEach { aAliasInd ->
                    val aAlias = aliasIdToAlias[aAliasInd]
                    val bSynonyms = varToAliasesVarsMap[bInd]!!
                    //                            if (methodName == "org.apache.logging.log4j.core.filter.StringMatchFilter#filter(org.apache.logging.log4j.core.Logger,org.apache.logging.log4j.Level,org.apache.logging.log4j.Marker,java.lang.String,java.lang.Object,java.lang.Object)") {
                    //                                println("bSyns sz: ${bSynonyms.cardinality()}") ////
                    //                            }
                    for (accs in accss) {
                        val newId = getAliasId(aAlias.withNewAccessors(accs))
                        for (bSynInd in bSynonyms.stream()) {
                            val bSynSet = varIndToSetOfAliases[bSynInd]!!
                            if (!bSynSet.get(newId)) {
                                bSynSet.set(newId)
                                if (storesAndLoads.contains(bSynInd) && !inQueue.get(bSynInd)) {
                                    queue.add(bSynInd)
                                    inQueue.set(bSynInd)
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private fun processGraphRibs(
        aInd: Int,
        aSet: BitSet,
        inQueue: BitSet,
        queue: IntArrayList
    ) {
        val bInd2Accs = storesAndLoads[aInd]
        if (bInd2Accs != null) {
            val iter = bInd2Accs.int2ObjectEntrySet().fastIterator()
            while (iter.hasNext()) {
                val entry = iter.next()
                val bInd = entry.intKey
                val accs = entry.value
                for (aAliasInd in aSet.stream()) {
                    val aAlias = aliasIdToAlias[aAliasInd]
                    val bSynonyms = varToAliasesVarsMap[bInd]!!
                    for (bSynInd in bSynonyms.stream()) {
                        val bSynSet = varIndToSetOfAliases[bSynInd]!!
                        for (acc in accs) {
                            val newId = getAliasId(aAlias.withNewAccessor(acc))
                            if (!bSynSet.get(newId)) {
                                bSynSet.set(newId)
                                if (storesAndLoads.contains(bSynInd) && !inQueue.get(bSynInd)) {
                                    queue.add(bSynInd)
                                    inQueue.set(bSynInd)
                                    //                                            if (methodName == "org.apache.logging.log4j.core.filter.StringMatchFilter#filter(org.apache.logging.log4j.core.Logger,org.apache.logging.log4j.Level,org.apache.logging.log4j.Marker,java.lang.Object,java.lang.Throwable)") {
                                    //                                                println("bSyns1 sz: ${bSynSet.cardinality()}") ////
                                    //                                            }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private fun load0() {
        for (ribN in 0..<currentF2fEdgesMapNum) {
            val alFId = currentF2fEdgesMapIdsFrom[ribN]
            val alTId = currentF2fEdgesMapIdsTo[ribN]
            if (alFId != alTId) {
                val alF = aliasIdToAlias[alFId]
//                if (true) { ////
//                    val t1 = aliasIdToAlias[alFId]
//                    val t2 = aliasIdToAlias[alTId]
//                    println("")
//                }
                if (depsWithCur.contains((alF.base as PointsToInstance).getMethodName())) {
                    okVars.set(currentF2fEdgesMapIdsFromVar[ribN])
                }
            }
        }
        for (zr in currentZ2FEdges) {
            if (depsWithCur.contains((zr.to.base as PointsToInstance).getMethodName())) {
                okVars.set(zr.indT)
            }
        }

        fun watch(pti: PointsToInstance, id: Int) {
            var ptiUpd = pti
            if (epVertices.get(id)) {
                ptiUpd = toEntryPoint(pti)
            }
            indToEntity[id] = ptiUpd
            entityToInd[ptiUpd] = id
            varToAliasesVarsMap.put(id, BitSet().let { it.set(id); it })
        }

        for ((id, pti) in ptis!!) {
            if (pti == null) {
                println("Unsupported value of $id")
            } else if (pti.isOkWithMethod(methodName, depsWithCur)) {
                okVars.clear(id)
                watch(pti, id)
            } else if (okVars.get(id)) {
                watch(pti, id)
            }
        }

        for (ribN in 0..<currentF2fEdgesMapNum) {
            val alFId = currentF2fEdgesMapIdsFrom[ribN]
            val alTId = currentF2fEdgesMapIdsTo[ribN]
            if (alFId != alTId) {
                val alF = aliasIdToAlias[alFId]
                val alT = aliasIdToAlias[alTId]
                if (depsWithCur.contains((alF.base as PointsToInstance).getMethodName())) {
                    val varId = currentF2fEdgesMapIdsFromVar[ribN]
                    val fInd = entityToInd.getInt(alF.base)
                    val tInd = entityToInd.getInt(alT.base)
                    multiStoresAndLoads.getOrPut(fInd) { Int2ObjectOpenHashMap() }.getOrPut(varId) { mutableSetOf() }
                        .add(alF.accessors)
                    multiStoresAndLoads.getOrPut(tInd) { Int2ObjectOpenHashMap() }.getOrPut(varId) { mutableSetOf() }
                        .add(alT.accessors)
                    multiStores.getOrPut(tInd) { Int2ObjectOpenHashMap() }.getOrPut(varId) { mutableSetOf() }
                        .add(alT.accessors)
                }
            }
        }
        for (zr in currentZ2FEdges) {
            if (depsWithCur.contains((zr.to.base as PointsToInstance).getMethodName())) {
                multiStoresAndLoads.getOrPut(entityToInd.getInt(zr.to)) { Int2ObjectOpenHashMap() }
                    .getOrPut(zr.indT) { mutableSetOf() }.add(zr.to.accessors)
                unknownToIds.getOrPut(zr.msg) { BitSet() }.set(zr.indT)
            }
        }
    }

    private fun load1() {
        val iter = indToEntity.int2ObjectEntrySet().fastIterator()
        val pList = pairList!!
        while (iter.hasNext()) {
            val entry = iter.next()
            val var1 = entry.intKey
            val ent1 = entry.value

            val var2Set = pList.get(var1)
                ?: continue

            var2Set.forEach { var2 ->
                val ent2 = indToEntity.get(var2)
                    ?: return@forEach

                if (ent1 is PointsToInstance.Unknown) {
                    unknownToIds.getOrPut(ent1.stdLibMethod) { BitSet() }.set(var2)
                } else {
                    varToAliasesVarsMap[var1]!!.set(var2) // reversed combination must be in file
                }
            }

        }
    }

    private fun load2() {
        for ((vars, items) in graphList!!) {
            val aInd = vars[0] // base
            val bInd = vars[1] //.field
            val entA = indToEntity[aInd]
            val entB = indToEntity[bInd]
            if (entA != null && entB != null && !okVars.get(aInd) && !okVars.get(bInd)) {
                val fInd = vars[2]
                val acc = fIndToAccessor[fInd]!!
                if (items[2] == "store_i") {
                    storesAndLoads.getOrPut(aInd) { Int2ObjectOpenHashMap() }.getOrPut(bInd) { mutableSetOf() }.add(acc)
                    stores.getOrPut(aInd) { Int2ObjectOpenHashMap() }.getOrPut(bInd) { mutableSetOf() }.add(acc)
                    // a.b = c // varToAliasesMap[aInd]!! varToAliasesMap[bInd]!!
                } else {
                    storesAndLoads.getOrPut(bInd) { Int2ObjectOpenHashMap() }.getOrPut(aInd) { mutableSetOf() }.add(acc)
                    // c -> a.b | a, b, c
                }
            }
        }
    }

    private fun load3() {
        for ((variable, vs) in varToAliasesVarsMap) {
            val aliases = BitSet()
            varIndToSetOfAliases[variable] = aliases
            val redundantAliases = BitSet()
            for (v in vs.stream()) {
                val entity = indToEntity[v]!!
                if (entity is AliasBase && (isCorrectBase(entity))) { // all is /AliasBase/, aliases only for args, rv, this or load - store ribs
                    if (entity.getMethodName() == methodName) {
                        val alias = Alias(entity, listOf())
                        val aliasId = getAliasId(alias)
                        aliases.set(aliasId)
                    }
                } else if (!loadStoreIncidentVs.get(v)) {
                    redundantAliases.set(v)
                }
            }
            vs.andNot(redundantAliases)
        }
    }

    private fun load4() {
        addAliasesUsingFields()
    }

    private fun loadPointsToInformation() {
        load0()
        load1()
        load2()
        load3()
        load4()
    }

    data class F2FEdge(val from: Alias, val to: Alias) {
        override fun toString(): String {
            return "$from -> $to"
        }

        fun printWithMethod(): String = "${from.printWithMethod()} -> ${to.printWithMethod()}"

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as F2FEdge

            if (from != other.from) return false
            if (to != other.to) return false

            return true
        }

        override fun hashCode(): Int {
            var result = from.hashCode()
            result = 31 * result + to.hashCode()
            return result
        }
    }

    data class Z2FEdge(val msg: String, val to: Alias, val indT: Int) {
        override fun toString(): String {
            return "$msg| $to"
        }

        fun printWithMethod(): String = "$msg| ${to.printWithMethod()}"

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (javaClass != other?.javaClass) return false

            other as Z2FEdge

            if (msg != other.msg) return false
            if (to != other.to) return false

            return true
        }

        override fun hashCode(): Int {
            var result = msg.hashCode()
            result = 31 * result + to.hashCode()
            return result
        }
    }

    fun isCorrectBase(base: AliasBase): Boolean {
        return isCorrectStartBase(base) || base is PointsToInstance.ReturnValue
    }

    fun isCorrectStartBase(base: AliasBase): Boolean {
        return base is PointsToInstance.This || base is PointsToInstance.Argument
    }

    fun findEdges(z2fs: MutableSet<Z2FEdge>) {
        findEdges0()
        findEdges1(z2fs)
    }

    private fun findEdges1(z2fs: MutableSet<Z2FEdge>) {
        for ((method, ids) in unknownToIds) {
            for (id in ids.stream()) {
                for (aid in varToAliasesVarsMap[id].stream()) {
                    val aliases = varIndToSetOfAliases[aid]
                    if (aliases != null) {
                        for (toAliasId in aliases.stream()) {
                            val toAlias = aliasIdToAlias[toAliasId]
                            z2fs.add(Z2FEdge(method, toAlias, aid))
                        }
                    }
                }
            }
        }
    }

    private inline fun <T> findEdgesUsingList(
        ribList: Int2ObjectOpenHashMap<Int2ObjectOpenHashMap<MutableSet<T>>>,
        action: Alias.(T) -> Alias
    ) {
        val iter = ribList.int2ObjectEntrySet().fastIterator()
        while (iter.hasNext()) {
            val entry = iter.next()
            val var1 = entry.intKey
            val toPredAliases = varIndToSetOfAliases[var1]!!
            val var2ToFields = entry.value
            val subIter = var2ToFields.int2ObjectEntrySet().fastIterator()
            while (subIter.hasNext()) {
                val subEntry = subIter.next()
                val var2 = subEntry.intKey
                val fromAliases = varIndToSetOfAliases[var2]!!
                val fields = subEntry.value
                toPredAliases.forEach { toPredAliasId ->
                    for (field in fields) {
                        val toPredAlias = aliasIdToAlias[toPredAliasId]
                        if (toPredAlias.base.getMethodName() == methodName) {
                            val toAlias = toPredAlias.action(field)
                            val toAliasId = getAliasId(toAlias)
                            fromAliases.forEach { fromAliasId ->
                                if (toAliasId != fromAliasId) {
                                    val fromAlias = aliasIdToAlias[fromAliasId]
                                    var fromSet = currentF2fEdgesMap.get(fromAliasId)
                                    if (fromSet == null) {
                                        fromSet = BitSet().also { currentF2fEdgesMap.put(fromAliasId, it) }
                                    }
                                    if (isCorrectStartBase(fromAlias.base) && fromAlias.base.getMethodName() == methodName) {
                                        if (!fromSet.get(toAliasId)) {
                                            currentF2fEdgesMapIdsFrom[currentF2fEdgesMapNum] = fromAliasId
                                            currentF2fEdgesMapIdsTo[currentF2fEdgesMapNum] = toAliasId
                                            currentF2fEdgesMapIdsFromVar[currentF2fEdgesMapNum] = var2
                                            fromSet.set(toAliasId)
                                            currentF2fEdgesMapNum++
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private fun findEdges0() {
        findEdgesUsingList(stores) { field ->
            this.withNewAccessor(field)
        }
        findEdgesUsingList(multiStores) { fields ->
            this.withNewAccessors(fields)
        }

        var rv = PointsToInstance.ReturnValue(methodName)
        var rvInd = entityToInd.getOrDefault(rv, -1)
        if (rvInd == -1) {
            rv = PointsToInstance.ReturnValue(methodName, isEntryPoint = true)
            rvInd = entityToInd.getOrDefault(rv, -1)
        }
        if (rvInd != -1) {
            rv = indToEntity[rvInd]!! as PointsToInstance.ReturnValue
            val rvAlias = Alias(rv, listOf())
            val rvAliasId = getAliasId(rvAlias)
            val aliases = varIndToSetOfAliases[rvInd]
            if (aliases != null) {
                for (fromAliasId in aliases.stream()) {
                    var fromSet = currentF2fEdgesMap.get(fromAliasId)
                    val fromAlias = aliasIdToAlias[fromAliasId]
                    if (fromSet == null) {
                        fromSet = BitSet().also { currentF2fEdgesMap.put(fromAliasId, it) }
                    }
                    if (isCorrectStartBase(fromAlias.base) && fromAlias.base.getMethodName() == methodName) {
                        if (!fromSet.get(fromAliasId)) {
                            currentF2fEdgesMapIdsFrom[currentF2fEdgesMapNum] = fromAliasId
                            currentF2fEdgesMapIdsTo[currentF2fEdgesMapNum] = rvAliasId
                            currentF2fEdgesMapIdsFromVar[currentF2fEdgesMapNum] = rvInd
                            fromSet.set(rvAliasId)
                            currentF2fEdgesMapNum++
                        }
                    }
                }
            }
        }
    }
}


inline fun BitSet.forEach(action: (Int) -> Unit) {
    var node = nextSetBit(0)
    while (node >= 0) {
        action(node)
        node = nextSetBit(node + 1)
    }
}
