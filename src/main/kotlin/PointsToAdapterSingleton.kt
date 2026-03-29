package ru.mylogininya

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import java.util.BitSet
import kotlin.io.path.Path
import kotlin.io.path.bufferedReader
import kotlin.io.path.div
import kotlin.io.path.listDirectoryEntries

typealias AliasTail = List<String>

class PointsToAdapterSingleton private constructor(val methodName: String, val depsWithCur: Set<String>) {
    companion object {
        val MAX_ACCESSORS: Int = 5 //5

        private val accsIdToAccessorsList = mutableListOf<AliasTail>()
        private val accessorsToId = Object2IntOpenHashMap<AliasTail>().also {
            it.defaultReturnValue(-1)
        }

        private fun getAccessorsId(accs: AliasTail): Int {
            val currentId = accessorsToId.getInt(accs)
            if (currentId != -1) return currentId
            val id = accsIdToAccessorsList.size
            accessorsToId.put(accs, id)
            accsIdToAccessorsList.add(accs)
            return id
        }

        data class F2FInternal(val fromVarId: Int, val toVarId: Int, val fromAlId: Int, val toAlId: Int)

        val mName2RibSet = mutableMapOf<String, MutableSet<F2FInternal>>()

        val methodList = mutableListOf<Pair<String, Set<String>>>()
        const val homeDirectory = "/home/nikita/process_taint_with_solver/taint_in_graph_no_field/graphs"

        val currentZ2FEdges = mutableSetOf<Z2FEdge>()
        val defaultEdges = mutableListOf<F2FEdge>()
        private val fIndToAccessor: MutableMap<Int, String> = mutableMapOf()
        var ptis: List<Pair<Int, PointsToInstance?>>? = null
        var pairList: Int2ObjectOpenHashMap<BitSet>? = null
        var graphList: List<Pair<List<Int>, List<String>>>? = null
        val loadStoreIncidentVs = BitSet()
        val epVertices = BitSet()
        val epId2Entity = mutableMapOf<Int, AliasBase>()

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

            val currentF2fEdges = mutableSetOf<F2FEdge>()

            for ((_, rbs) in mName2RibSet) {
                for (r in rbs) {
                    if (epId2Entity[r.fromVarId] != null) {
                        currentF2fEdges.add(
                            F2FEdge(
                                Alias(epId2Entity[r.fromVarId]!!, accsIdToAccessorsList[r.fromAlId]),
                                Alias(epId2Entity[r.toVarId]!!, accsIdToAccessorsList[r.toAlId]),
                            )
                        )
                    }
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
            if (name.contains("<")) {
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

    private val unknownToIds: MutableMap<String, BitSet> = mutableMapOf()


    val currentStartBases: MutableList<Int> = mutableListOf()
    val endBases: BitSet = BitSet()

    val loadsFrom: Int2ObjectOpenHashMap<BitSet> = Int2ObjectOpenHashMap()
    val loadsTo: Int2ObjectOpenHashMap<BitSet> = Int2ObjectOpenHashMap()
    val loadId2Acc: Int2ObjectOpenHashMap<String> = Int2ObjectOpenHashMap()
    val loadId2End: Int2ObjectOpenHashMap<Int> = Int2ObjectOpenHashMap()
    val loadId2Start: Int2ObjectOpenHashMap<Int> = Int2ObjectOpenHashMap()
    var loadRibNum = 0

    val storesFrom: Int2ObjectOpenHashMap<BitSet> = Int2ObjectOpenHashMap()
    val storeId2Acc: Int2ObjectOpenHashMap<String> = Int2ObjectOpenHashMap()
    val storeId2End: Int2ObjectOpenHashMap<Int> = Int2ObjectOpenHashMap()
    var storesRibNum = 0

    val srFrom: Int2ObjectOpenHashMap<BitSet> = Int2ObjectOpenHashMap()
    val srTo: Int2ObjectOpenHashMap<BitSet> = Int2ObjectOpenHashMap()
    val sr2Al1: Int2ObjectOpenHashMap<Int> = Int2ObjectOpenHashMap()
    val sr2Al2: Int2ObjectOpenHashMap<Int> = Int2ObjectOpenHashMap()
    val sr2Start: Int2ObjectOpenHashMap<Int> = Int2ObjectOpenHashMap()
    val sr2End: Int2ObjectOpenHashMap<Int> = Int2ObjectOpenHashMap()
    var srRibNum = 0

    init {
        loadPointsToInformation()
    }


//    println(
    //            "Summary ribs: ${
//                multiStoresAndLoads.map { i -> i.value.map { j -> j.value.size }.sum() }.sum()
//            } Graph: ${storesAndLoads.map { i -> i.value.map { j -> j.value.size }.sum() }.sum()}"
//        ) ////

    private fun load0() {
        mName2RibSet[methodName] = mutableSetOf()
        for (dep in depsWithCur) {
            for (r in mName2RibSet[dep]!!) {
                srFrom.getOrPut(r.fromVarId) { BitSet() }.set(srRibNum)
                srTo.getOrPut(r.toVarId) { BitSet() }.set(srRibNum)
                sr2Start[srRibNum] = r.fromVarId
                sr2End[srRibNum] = r.toVarId
                sr2Al1[srRibNum] = r.fromAlId
                sr2Al2[srRibNum] = r.toAlId
                srRibNum++
            }
        }
//        for (ribN in 0..<currentF2fEdgesMapNum) {
//            val alFId = currentF2fEdgesMapIdsFrom[ribN]
//            val alTId = currentF2fEdgesMapIdsTo[ribN]
//            if (alFId != alTId) {
//                val alF = aliasIdToAlias[alFId]
//                if (depsWithCur.contains((alF.base as PointsToInstance).getMethodName())) {
//                    okVars.set(currentF2fEdgesMapIdsFromVar[ribN])
//                }
//            }
//        }
//        for (zr in currentZ2FEdges) {
//            if (depsWithCur.contains((zr.to.base as PointsToInstance).getMethodName())) {
//                okVars.set(zr.indT)
//            }
//        }

        fun watch(pti: PointsToInstance, id: Int) {
            var ptiUpd = pti
            if (epVertices.get(id)) {
                ptiUpd = toEntryPoint(pti)
                epId2Entity[id] = (ptiUpd as AliasBase)
            }
            indToEntity[id] = ptiUpd
            entityToInd[ptiUpd] = id
            varToAliasesVarsMap.put(id, BitSet().let { it.set(id); it })
        }

        for ((id, pti) in ptis!!) {
            if (pti == null) {
                println("Unsupported value of $id")
            } else if (pti.isOkWithMethod(methodName, depsWithCur)) {
                // okVars.clear(id)
                watch(pti, id)
            } //else if (okVars.get(id)) {
//                watch(pti, id)
//            }
        }

//        for (ribN in 0..<currentF2fEdgesMapNum) {
//            val alFId = currentF2fEdgesMapIdsFrom[ribN]
//            val alTId = currentF2fEdgesMapIdsTo[ribN]
//            if (alFId != alTId) {
//                val alF = aliasIdToAlias[alFId]
//                val alT = aliasIdToAlias[alTId]
//                if (depsWithCur.contains((alF.base as PointsToInstance).getMethodName())) {
//                    val varId = currentF2fEdgesMapIdsFromVar[ribN]
//                    val fInd = entityToInd.getInt(alF.base)
//                    val tInd = entityToInd.getInt(alT.base)
//                    multiStoresAndLoads.getOrPut(fInd) { Int2ObjectOpenHashMap() }.getOrPut(varId) { mutableSetOf() }
//                        .add(alF.accessors)
//                    multiStoresAndLoads.getOrPut(tInd) { Int2ObjectOpenHashMap() }.getOrPut(varId) { mutableSetOf() }
//                        .add(alT.accessors)
//                    multiStores.getOrPut(tInd) { Int2ObjectOpenHashMap() }.getOrPut(varId) { mutableSetOf() }
//                        .add(alT.accessors)
//                }
//            }
//        }
//        for (zr in currentZ2FEdges) {
//            if (depsWithCur.contains((zr.to.base as PointsToInstance).getMethodName())) {
//                multiStoresAndLoads.getOrPut(entityToInd.getInt(zr.to)) { Int2ObjectOpenHashMap() }
//                    .getOrPut(zr.indT) { mutableSetOf() }.add(zr.to.accessors)
//                unknownToIds.getOrPut(zr.msg) { BitSet() }.set(zr.indT)
//            }
//        }
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
            if (entA != null && entB != null) {
                val fInd = vars[2]
                val acc = fIndToAccessor[fInd]!!
                if (items[2] == "store_i") {
                    storesFrom.getOrPut(bInd) { BitSet() }.set(storesRibNum)
                    storeId2Acc[storesRibNum] = acc
                    storeId2End[storesRibNum] = aInd
                    storesRibNum++

//                    storesAndLoads.getOrPut(aInd) { Int2ObjectOpenHashMap() }.getOrPut(bInd) { mutableSetOf() }.add(acc)
//                    stores.getOrPut(aInd) { Int2ObjectOpenHashMap() }.getOrPut(bInd) { mutableSetOf() }.add(acc)
                    // a.b = c // varToAliasesMap[aInd]!! varToAliasesMap[bInd]!!
                } else {
                    loadsFrom.getOrPut(aInd) { BitSet() } .set(loadRibNum)
                    loadsTo.getOrPut(bInd) { BitSet() } .set(loadRibNum)
                    loadId2Acc[loadRibNum] = acc
                    loadId2Start[loadRibNum] = aInd
                    loadId2End[loadRibNum] = bInd
                    loadRibNum++

//                    storesAndLoads.getOrPut(bInd) { Int2ObjectOpenHashMap() }.getOrPut(aInd) { mutableSetOf() }.add(acc)
                    // c -> a.b | a, b, c
                }
            }
        }
    }

    private fun load3() {
        for ((variable, vs) in varToAliasesVarsMap) {
            val redundantAliases = BitSet()
            for (v in vs.stream()) {
                val entity = indToEntity[v]!!
                if (entity is AliasBase && (isCorrectBase(entity))) { // all is /AliasBase/, aliases only for args, rv, this or load - store ribs
                    if (entity.getMethodName() == methodName) {
                        endBases.set(v)
                        if (isCorrectStartBase(entity)) {
                            currentStartBases.add(v)
                        }
//                        val alias = Alias(entity, listOf())
//                        val aliasId = getAliasId(alias)
//                        aliases.set(aliasId)
                    }
                } else if (!loadStoreIncidentVs.get(v)) {
                    redundantAliases.set(v)
                }
            }
            vs.andNot(redundantAliases)
        }
    }

    private fun loadPointsToInformation() {
        load0()
        load1()
        load2()
        load3()
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
        // TODO: local aliases after testing
        val stackToWatch = IntArrayList()
        while (currentStartBases.isNotEmpty()) { // TODO: dublicate
            val beginId = currentStartBases.removeLast()
            stackToWatch.add(beginId)
            val emptyListId = getAccessorsId(listOf())
            stackToWatch.add(emptyListId)
            stackToWatch.add(emptyListId)
            stackToWatch.add(-1)
            stackToWatch.add(0)
            while (!stackToWatch.isEmpty()) {
                val varId = stackToWatch.getOrElse(stackToWatch.size - 5) { -1 }
                val al1 = stackToWatch.getOrElse(stackToWatch.size - 4) { -1 }
                val al2 = stackToWatch.getOrElse(stackToWatch.size - 3) { -1 }
                val nxt = stackToWatch.getOrElse(stackToWatch.size - 2) { -1 }
                val wasStore = stackToWatch.getOrElse(stackToWatch.size - 1) { -1 }
                if (stackToWatch.size % 5 != 0) {
                    throw IllegalStateException("stack size")
                }
                if (stackToWatch.size % 10 == 5) {
                    val newNext = varToAliasesVarsMap[varId].nextSetBit(nxt + 1)
                    if (newNext == -1) {
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        continue
                    }
                    stackToWatch[stackToWatch.size - 2] = newNext
                    stackToWatch.add(newNext)
                    stackToWatch.add(al1)
                    stackToWatch.add(al2)
                    stackToWatch.add(-1)
                    stackToWatch.add(wasStore)
                    if (endBases.get(newNext)) {
                        mName2RibSet[methodName]!!.add(F2FInternal(beginId, newNext, al1, al2))
                    }
                } else if (wasStore == 0) {
                    val newNext = loadsFrom[varId]?.nextSetBit(nxt + 1) ?: -1
                    val accessors = accsIdToAccessorsList[al1]
                    if (newNext == -1 || accessors.size >= MAX_ACCESSORS) {
                        stackToWatch[stackToWatch.size - 1] = 1
                        continue
                    }
                    stackToWatch[stackToWatch.size - 2] = newNext
                    val newVar = loadId2End[newNext]
                    stackToWatch.add(newVar)
                    val acc = loadId2Acc[newNext]
                    val newAl = getAccessorsId(accessors + acc)
                    stackToWatch.add(newAl)
                    stackToWatch.add(al2)
                    stackToWatch.add(-1)
                    stackToWatch.add(0)
                } else if (wasStore == 1) {
                    val newNext = storesFrom[varId]?.nextSetBit(nxt + 1) ?: -1
                    val accessors = accsIdToAccessorsList[al2]
                    if (newNext == -1 || accessors.size >= MAX_ACCESSORS) {
                        stackToWatch[stackToWatch.size - 1] = 2
                        continue
                    }
                    stackToWatch[stackToWatch.size - 2] = newNext
                    val newVar = storeId2End[newNext]
                    stackToWatch.add(newVar)
                    val acc = storeId2Acc[newNext]
                    val newAl = getAccessorsId(listOf(acc) + accessors)
                    stackToWatch.add(al1)
                    stackToWatch.add(newAl)
                    stackToWatch.add(-1)
                    stackToWatch.add(4)
                } else if (wasStore == 2) {
                    val newNext = srFrom[varId]?.nextSetBit(nxt + 1) ?: -1
                    val accessorsHaveFrom = accsIdToAccessorsList[al1]
                    val accessorsHaveTo = accsIdToAccessorsList[al2]
                    if (newNext == -1) {
                        stackToWatch[stackToWatch.size - 1] = 3
                        continue
                    }
                    stackToWatch[stackToWatch.size - 2] = newNext
                    val newVar = sr2End[newNext]
                    val accessorsFrom = accsIdToAccessorsList[sr2Al1[newNext]]
                    val accessorsTo = accsIdToAccessorsList[sr2Al2[newNext]]

                    val addToHaveFrom = if (accessorsFrom.size > accessorsHaveTo.size) {
                        accessorsFrom.drop(accessorsHaveTo.size)
                    } else {
                        listOf<String>()
                    }
                    val addToHaveTo = if (accessorsFrom.size < accessorsHaveTo.size) {
                        accessorsHaveTo.drop(accessorsFrom.size)
                    } else {
                        listOf<String>()
                    }
                    val midAccessors = accessorsFrom.take(accessorsHaveTo.size)
                    if (getAccessorsId(midAccessors) != al2
                        || accessorsHaveFrom.size + addToHaveFrom.size > MAX_ACCESSORS
                        || accessorsTo.size + addToHaveTo.size > MAX_ACCESSORS) {
                        continue
                    }

                    val newAl1 = getAccessorsId(accessorsHaveFrom + addToHaveFrom)
                    val newAl2 = getAccessorsId(accessorsTo + addToHaveTo)
                    stackToWatch.add(newVar)
                    stackToWatch.add(newAl1)
                    stackToWatch.add(newAl2)
                    stackToWatch.add(-1)
                    stackToWatch.add(0)
                } else if (wasStore == 3) {
                    val newNext = srFrom[varId]?.nextSetBit(nxt + 1) ?: -1
                    val accessorsHaveFrom = accsIdToAccessorsList[al1]
                    val accessorsHaveTo = accsIdToAccessorsList[al2]
                    if (newNext == -1) {
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        continue
                    }
                    stackToWatch[stackToWatch.size - 2] = newNext
                    val newVar = sr2End[newNext]
                    val accessorsFrom = accsIdToAccessorsList[sr2Al1[newNext]]
                    val accessorsTo = accsIdToAccessorsList[sr2Al2[newNext]]

                    val addToHaveFrom = if (accessorsFrom.size > accessorsHaveTo.size) {
                        accessorsFrom.drop(accessorsHaveTo.size)
                    } else {
                        listOf<String>()
                    }
                    val addToHaveTo = if (accessorsFrom.size < accessorsHaveTo.size) {
                        accessorsHaveTo.drop(accessorsFrom.size)
                    } else {
                        listOf<String>()
                    }
                    val midAccessors = accessorsFrom.take(accessorsHaveTo.size)
                    if (getAccessorsId(midAccessors) != al2
                        || accessorsHaveFrom.size + addToHaveFrom.size > MAX_ACCESSORS
                        || accessorsTo.size + addToHaveTo.size > MAX_ACCESSORS) {
                        continue
                    }

                    val newAl1 = getAccessorsId(accessorsHaveFrom + addToHaveFrom)
                    val newAl2 = getAccessorsId(accessorsTo + addToHaveTo)
                    stackToWatch.add(newVar)
                    stackToWatch.add(newAl1)
                    stackToWatch.add(newAl2)
                    stackToWatch.add(-1)
                    stackToWatch.add(4)
                } else if (wasStore == 4) {
                    val newNext = loadsTo[varId]?.nextSetBit(nxt + 1) ?: -1
                    val accessors = accsIdToAccessorsList[al2]
                    if (newNext == -1 || accessors.size >= MAX_ACCESSORS) {
                        stackToWatch[stackToWatch.size - 1] = 5
                        continue
                    }
                    stackToWatch[stackToWatch.size - 2] = newNext
                    val newVar = loadId2Start[newNext]
                    stackToWatch.add(newVar)
                    val acc = loadId2Acc[newNext]
                    val newAl = getAccessorsId(listOf(acc) + accessors)
                    stackToWatch.add(al1)
                    stackToWatch.add(newAl)
                    stackToWatch.add(-1)
                    stackToWatch.add(4)
                } else if (wasStore == 5) {
                    val newNext = srTo[varId]?.nextSetBit(nxt + 1) ?: -1
                    val accessorsHaveFrom = accsIdToAccessorsList[al1]
                    val accessorsHaveTo = accsIdToAccessorsList[al2]
                    if (newNext == -1) {
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        stackToWatch.removeLast()
                        continue
                    }
                    stackToWatch[stackToWatch.size - 2] = newNext
                    val newVar = sr2Start[newNext]
                    val accessorsFrom = accsIdToAccessorsList[sr2Al2[newNext]]
                    val accessorsTo = accsIdToAccessorsList[sr2Al1[newNext]]

                    val addToHaveFrom = if (accessorsFrom.size > accessorsHaveTo.size) {
                        accessorsFrom.drop(accessorsHaveTo.size)
                    } else {
                        listOf<String>()
                    }
                    val addToHaveTo = if (accessorsFrom.size < accessorsHaveTo.size) {
                        accessorsHaveTo.drop(accessorsFrom.size)
                    } else {
                        listOf<String>()
                    }
                    val midAccessors = accessorsFrom.take(accessorsHaveTo.size)
                    if (getAccessorsId(midAccessors) != al2
                        || accessorsHaveFrom.size + addToHaveFrom.size > MAX_ACCESSORS
                        || accessorsTo.size + addToHaveTo.size > MAX_ACCESSORS) {
                        continue
                    }

                    val newAl1 = getAccessorsId(accessorsHaveFrom + addToHaveFrom)
                    val newAl2 = getAccessorsId(accessorsTo + addToHaveTo)
                    stackToWatch.add(newVar)
                    stackToWatch.add(newAl1)
                    stackToWatch.add(newAl2)
                    stackToWatch.add(-1)
                    stackToWatch.add(4)
                } else {
                    throw IllegalStateException("was store")
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
