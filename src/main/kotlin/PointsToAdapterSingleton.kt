package ru.mylogininya

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import java.util.BitSet
import kotlin.io.path.Path
import kotlin.io.path.bufferedReader
import kotlin.io.path.div
import kotlin.io.path.listDirectoryEntries

class PointsToAdapterSingleton private constructor(val methodName: String, val depsWithCur: Set<String>) {
    companion object {
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
        const val homeDirectory = "/home/nikita/process_taint_with_solver/taint_in_graph_no_field/graphs"

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
                    val (m, ms) = line.split("  ")
                    methodList.add(Pair(m, (ms.split(" ") + m).toSet()))
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
                        gList.add(listOf(items[0], items[1], items[3]).map { it.toInt() * countDirEntries + dirId }.toList() to items)
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
                PointsToAdapterSingleton(method, depsWithCur).findEdges(currentF2fEdgesMap, currentZ2FEdges)
                methodId += 1 /////
            }

            val currentF2fEdges = mutableListOf<F2FEdge>()

            for ((fromAliasId, toAliasSet) in currentF2fEdgesMap){
                toAliasSet.forEach { toAliasId ->
                    val fromAlias = aliasIdToAlias[fromAliasId]
                    val toAlias = aliasIdToAlias[toAliasId]
                    currentF2fEdges.add(F2FEdge(fromAlias, toAlias))
                }
            }

            currentF2fEdges.addAll(defaultEdges)
            return currentF2fEdges.filter {
                val from = it.from.base
                when (from) {
                    is PointsToInstance.Argument -> from.isEntryPoint
                    is PointsToInstance.ReturnValue -> from.isEntryPoint
                    is PointsToInstance.This -> from.isEntryPoint
                    else -> throw IllegalArgumentException("Unsupported alias base")
                }
            }.toList() to
                    currentZ2FEdges.filter {
                        val to = it.to.base
                        when (to) {
                            is PointsToInstance.Argument -> to.isEntryPoint
                            is PointsToInstance.ReturnValue -> to.isEntryPoint
                            is PointsToInstance.This -> to.isEntryPoint
                            else -> throw IllegalArgumentException("Unsupported alias base")
                        }
                    }.toList()
        }
    }

    sealed interface AliasBase {
        fun getMethodName(): String

        fun getMethodUnifiedName(): String {
            val name = getMethodName()
            if (!(this is PointsToInstance.This || this is PointsToInstance.Argument || this is PointsToInstance.ReturnValue)) {
                throw IllegalStateException("must not be this, arg, rv")
            }
            if (name.contains("<")) {
                throw IllegalStateException("must not contain <")
            }
            val (mName, args) = name.split(")", limit=2)[1].split("(", limit=2)
            val methodName = "$mName(${args.replace("$", ".")}"
            return methodName.replace("#", "::").replace(", ", ",")
        }
    }

    sealed interface PointsToInstance {
        fun getMethodName(): String
        fun isOkWithMethod(m: String, ms: Set<String>): Boolean = getMethodName() == m

        data class Rubbish(val u: Int, val methodOrEmpty: String = "", val isOkAlways: Boolean = false) : PointsToInstance, AliasBase {
            override fun getMethodName(): String {
                throw IllegalStateException("must not be Rubbish")
            }

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
        data class Argument(val method: String, val index: Int, val isEntryPoint: Boolean = false) : PointsToInstance, AliasBase {
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
            if (accessors.size >= 5) {
                return this
            }
            return Alias(base, accessors + accessor)
        }

        fun withNewAccessors(accessorList: List<String>): Alias {
            if (accessors.size >= 5) {
                return this
            }
            return Alias(base, accessors + accessorList.take(5 - accessors.size))
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

    private val varToAliasesMap = Int2ObjectOpenHashMap<BitSet>()
    private val indToEntity = Int2ObjectOpenHashMap<PointsToInstance>()
    private val entityToInd = Object2IntOpenHashMap<PointsToInstance>()
    private val storesAndLoads: MutableList<Triple<Int, String, Int>> = mutableListOf()
    private val loads: MutableList<Triple<Int, String, Int>> = mutableListOf()
    private val varIndToSetOfAliases: MutableMap<Int, BitSet> = mutableMapOf()
    private val varIndToLoadSetOfAliases: MutableMap<Int, BitSet> = mutableMapOf()
    private val unknownToIds: MutableMap<String, BitSet> = mutableMapOf()

    //private val aliasIdToVarIds: MutableMap<Int, BitSet> = mutableMapOf()

    val okVars = BitSet()
    val multiStoresAndLoads = mutableSetOf<Triple<Int, List<String>, Int>>()
    val multiLoads = mutableSetOf<Triple<Int, List<String>, Int>>()
    init {
        loadPointsToInformation()
    }

    private fun addAliasesUsingFields(forStores: Boolean) {
        var indToSetOfAliasesSize = createIndToSetOfAliasesSize(forStores)
        val correspondingMap = if (forStores) varIndToSetOfAliases else varIndToLoadSetOfAliases
        val multiRibs = if (forStores) multiStoresAndLoads else multiLoads
        val graphRibs = if (forStores) storesAndLoads else loads
        var wasChanges = true

//        var progressWhile = 0 /////
        while (wasChanges) {
//            progressWhile += 1
//            println("While: $progressWhile") /////
//            var progressRibs = 0 /////
//            var progressChanges = 0 /////
            for ((aInd, acc, bInd) in graphRibs) {
//                progressRibs += 1 /////
//                if (progressRibs % 10000 == 1) {
//                    println("Ribs: $progressRibs Changes: $progressChanges") /////
//                }
                val aSet = correspondingMap[aInd]!!
                for (aAliasInd in aSet.stream()) {
                    val aAlias = aliasIdToAlias[aAliasInd]
                    if (isCorrectBase(aAlias.base)) {
                        val bSynonyms = varToAliasesMap[bInd]!!
                        for (bSynInd in bSynonyms.stream()) {
                            val bSynSet = correspondingMap[bSynInd]!!
                            bSynSet.set(getAliasId(aAlias.withNewAccessor(acc)))
//                            progressChanges += 1 /////
                        }
                    }
                }
            }
            for ((aInd, acs, bInd) in multiRibs) {
                val aSet = correspondingMap[aInd]!!
                for (aAliasInd in aSet.stream()) {
                    val aAlias = aliasIdToAlias[aAliasInd]
                    if (isCorrectBase(aAlias.base)) {
                        val bSynonyms = varToAliasesMap[bInd]!!
                        for (bSynInd in bSynonyms.stream()) {
                            val bSynSet = correspondingMap[bSynInd]!!
                            bSynSet.set(getAliasId(aAlias.withNewAccessors(acs)))
//                            progressChanges += 1 /////
                        }
                    }
                }
            }
            val newIndToSetOfAliasesSize = createIndToSetOfAliasesSize(forStores)
            if (indToSetOfAliasesSize == newIndToSetOfAliasesSize) {
                wasChanges = false
            }
            indToSetOfAliasesSize = newIndToSetOfAliasesSize
        }
    }

    private fun createIndToSetOfAliasesSize(forStores: Boolean): Map<Int, Int> {
        if (forStores) {
            return varIndToSetOfAliases.mapValues { value -> value.value.cardinality() }
        }
        return varIndToLoadSetOfAliases.mapValues { value -> value.value.cardinality() }
    }

    private fun load0() {
        for (ribN in 0..<currentF2fEdgesMapNum) {
            val alFId = currentF2fEdgesMapIdsFrom[ribN]
            val alTId = currentF2fEdgesMapIdsTo[ribN]
            if (alFId != alTId) {
                val alF = aliasIdToAlias[alFId]
                if ((alF.base as PointsToInstance).isOkWithMethod(methodName, depsWithCur)) {
                    okVars.set(currentF2fEdgesMapIdsFromVar[ribN])
                }
            }
        }
        for (zr in currentZ2FEdges) {
            if ((zr.to.base as PointsToInstance).isOkWithMethod(methodName, depsWithCur)) {
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
            varToAliasesMap.put(id, BitSet().let { it.set(id); it })
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
                if ((alF.base as PointsToInstance).isOkWithMethod(methodName, depsWithCur)) {
                    val varId = currentF2fEdgesMapIdsFromVar[ribN]
                    val fInd = entityToInd.getInt(alF.base)
                    val tInd = entityToInd.getInt(alT.base)
                    multiLoads.add(Triple(fInd, alF.accessors, varId))
                    multiStoresAndLoads.add(Triple(fInd, alF.accessors, varId))
                    multiStoresAndLoads.add(Triple(tInd, alT.accessors, varId))
                }
            }
        }
        for (zr in currentZ2FEdges) {
            if ((zr.to.base as PointsToInstance).isOkWithMethod(methodName, depsWithCur)) {
                multiStoresAndLoads.add(Triple(aliasToId.getInt(zr.to), zr.to.accessors, zr.indT))
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
                    varToAliasesMap[var1]!!.set(var2) // reversed combination must be in file
                }
            }

        }
//        for ((var1, var2) in pairList!!) {
//            val ent1 = indToEntity[var1]
//            val ent2 = indToEntity[var2]
//            if (ent1 != null && ent2 != null) {
//                if (ent1 is PointsToInstance.Unknown) {
//                    unknownToIds.getOrPut(ent1.stdLibMethod) { BitSet() }.set(var2)
//                } else {
//                    varToAliasesMap[var1]!!.set(var2) // reversed combination must be in file
//                }
//            }
//        }
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
                    storesAndLoads.add(
                        Triple(
                            aInd,
                            acc,
                            bInd
                        )
                    ) // a.b = c // varToAliasesMap[aInd]!! varToAliasesMap[bInd]!!
                } else {
                    storesAndLoads.add(Triple(bInd, acc, aInd))
                    loads.add(Triple(bInd, acc, aInd)) // c -> a.b | a, b, c
                }
            }
        }
    }

    private fun load3() {
        for ((variable, vs) in varToAliasesMap) {
            val aliases = BitSet()
            varIndToSetOfAliases[variable] = aliases
            val redundantAliases = BitSet()
            for (v in vs.stream()) {
                val entity = indToEntity[v]!!
                if (entity is AliasBase && (isCorrectBase(entity))) { // all is /AliasBase/, aliases only for args, rv, this or load - store ribs
                    val alias = Alias(entity, listOf())
                    val aliasId = getAliasId(alias)
                    //aliasIdToVarIds.getOrPut(aliasId) { BitSet() }.set(v);
                    aliases.set(aliasId)
                } else if (!loadStoreIncidentVs.get(v)){
                    redundantAliases.set(v)
                }
            }
            vs.andNot(redundantAliases)
            varIndToLoadSetOfAliases[variable] = aliases.clone() as BitSet
        }
    }

    private fun load4() {
        addAliasesUsingFields(false)
    }

//    private fun loadF2FEdges() {
//        val iter = currentF2fEdgesMap.int2ObjectEntrySet().fastIterator()
//        while (iter.hasNext()) {
//            val entry = iter.next()
//            val fromId = entry.intKey
//            val fromVars = aliasIdToVarIds[fromId] ?: continue
//
//            val toAlSet = entry.value
//
//            toAlSet.forEach { toId ->
//                if (fromId == toId) return@forEach
//
//                val toVars = aliasIdToVarIds[toId] ?: return@forEach
//
//                for (var1 in fromVars.stream()) {
//                    for (var2 in toVars.stream()) {
//                        val var1AliasesMap: BitSet = varToAliasesMap[var1]!!.clone() as BitSet
//                        val var2AliasesMap = varToAliasesMap[var2]!!.clone() as BitSet
//                        val var1SetOfAliases = varIndToSetOfAliases[var1]!!.clone() as BitSet
//                        val var2SetOfAliases = varIndToSetOfAliases[var2]!!.clone() as BitSet
//                        for (var1AliasObj in var1SetOfAliases.stream()) {
//                            aliasIdToVarIds.getOrPut(var1AliasObj) { BitSet() }.or(var2AliasesMap)
//                        }
//                        for (var2AliasObj in var2SetOfAliases.stream()) {
//                            aliasIdToVarIds.getOrPut(var2AliasObj) { BitSet() }.or(var1AliasesMap)
//                        }
//                        for (var1Alias in var1AliasesMap.stream()) {
//                            varToAliasesMap[var1Alias]!!.or(var2AliasesMap)
//                            varIndToSetOfAliases[var1Alias]!!.or(var2SetOfAliases)
//                        }
//                        for (var2Alias in var2AliasesMap.stream()) {
//                            varToAliasesMap[var2Alias]!!.or(var1AliasesMap)
//                            varIndToSetOfAliases[var2Alias]!!.or(var1SetOfAliases)
//                        }
//                    }
//                }
//            }
//        }
//    }

    private fun load6() {
        addAliasesUsingFields(true)
    }

    private fun loadPointsToInformation() {
        load0()
        load1()
        load2()
        load3()
        load4()
        //loadF2FEdges()
        load6()
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

    fun findEdges(f2fs: Int2ObjectOpenHashMap<BitSet>, z2fs: MutableSet<Z2FEdge>) {
        findEdges0()
        findEdges1(z2fs)
//        findEdges2(z2fs)
    }

//    private fun findEdges2(z2fs: MutableSet<Z2FEdge>) {
//        for ((method, al) in currentZ2FEdges.toList()) {
//            val alId = getAliasId(al)
//            if (aliasIdToVarIds.containsKey(alId)) {
//                for (id in aliasIdToVarIds[alId]!!.stream()) {
//                    val aliases = varIndToSetOfAliases[id]
//                    if (aliases != null) {
//                        for (toAliasId in aliases.stream()) {
//                            val toAlias = aliasIdToAlias[toAliasId]
//                            if (isCorrectBase(toAlias.base)) {
//                                z2fs.add(Z2FEdge(method, toAlias))
//                            }
//                        }
//                    }
//                }
//            }
//        }
//    }

    private fun findEdges1(z2fs: MutableSet<Z2FEdge>) {
        for ((method, ids) in unknownToIds) {
            for (id in ids.stream()) {
                val aliases = varIndToSetOfAliases[id]
                if (aliases != null) {
                    for (toAliasId in aliases.stream()) {
                        val toAlias = aliasIdToAlias[toAliasId]
                        if (isCorrectBase(toAlias.base)) {
                            z2fs.add(Z2FEdge(method, toAlias, id))
                        }
                    }
                }
            }
        }
    }

    private fun findEdges0() {
        for ((varInd, aliases) in varIndToSetOfAliases) {
            val fromAliases = varIndToLoadSetOfAliases[varInd]!!
            for (fromAliasId in fromAliases.stream()) {
                val fromAlias = aliasIdToAlias[fromAliasId]
                if (isCorrectStartBase(fromAlias.base)) {
                    var fromSet = currentF2fEdgesMap.get(fromAliasId)
                    if (fromSet == null) {
                        fromSet = BitSet().also { currentF2fEdgesMap.put(fromAliasId, it) }
                    }

                    for (toAliasId in aliases.stream()) {
                        val toAlias = aliasIdToAlias[toAliasId]
                        if (isCorrectBase(toAlias.base)
                            && toAlias.base.getMethodName() == methodName
                            && fromAlias.base.getMethodName() == methodName
                        ) {
                            if (!fromSet.get(toAliasId)) {
                                currentF2fEdgesMapIdsFrom[currentF2fEdgesMapNum] = fromAliasId
                                currentF2fEdgesMapIdsTo[currentF2fEdgesMapNum] = toAliasId
                                currentF2fEdgesMapIdsFromVar[currentF2fEdgesMapNum] = varInd
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


inline fun BitSet.forEach(action: (Int) -> Unit) {
    var node = nextSetBit(0)
    while (node >= 0) {
        action(node)
        node = nextSetBit(node + 1)
    }
}
