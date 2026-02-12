package ru.mylogininya

import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import java.util.BitSet
import kotlin.io.path.Path
import kotlin.io.path.bufferedReader
import kotlin.io.path.div
import kotlin.io.path.listDirectoryEntries

class PointsToAdapterSingleton private constructor(val methodName: String) {
    init {
        loadPointsToInformation(homeDirectory)
    }

    companion object {
        val methodList = mutableListOf<String>()
        const val homeDirectory = "/home/nikita/process_taint_with_solver/taint_in_graph_no_field/graphs"
        val currentF2fEdges = mutableListOf<F2FEdge>()
        val defaultEdges = mutableListOf<F2FEdge>()
        private val fIndToAccessor: MutableMap<Int, String> = mutableMapOf()

        init {
            val countDirEntries = Path(homeDirectory).listDirectoryEntries().count()
            var dirId = 0
            Path(homeDirectory).listDirectoryEntries().forEach { projectDirectory ->
                (projectDirectory / "full_methods_list.txt").bufferedReader().forEachLine { line ->
                    methodList.add(line)
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
                dirId += 1
            }
        }

        fun findEdges(): Pair<List<F2FEdge>, List<Z2FEdge>> {
            TODO()
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
        fun isOkWithMethod(m: String): Boolean = getMethodName() == m

        data class Rubbish(val u: Int, val appropriate: Boolean) : PointsToInstance, AliasBase {
            override fun getMethodName(): String {
                throw IllegalStateException("must not be Rubbish")
            }

            override fun isOkWithMethod(m: String): Boolean = appropriate
        }

        data class This(val method: String, val isEntryPoint: Boolean = false) : PointsToInstance, AliasBase {
            override fun toString(): String = "this"
            override fun getMethodName(): String = method
            override fun isOkWithMethod(m: String): Boolean = true
        }
        data class LocalVar(val method: String, val index: Int) : PointsToInstance, AliasBase {
            override fun getMethodName(): String = method
        }
        data class Argument(val method: String, val index: Int, val isEntryPoint: Boolean = false) : PointsToInstance, AliasBase {
            override fun toString(): String = "arg($index)"
            override fun getMethodName(): String = method
            override fun isOkWithMethod(m: String): Boolean = true
        }
        data class ReturnValue(val method: String, val isEntryPoint: Boolean = false) : PointsToInstance, AliasBase {
            override fun toString(): String = "return"
            override fun getMethodName(): String = method
            override fun isOkWithMethod(m: String): Boolean = true
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

    private val varToAliasesMap = mutableMapOf<Int, BitSet>()
    private val indToEntity = mutableMapOf<Int, PointsToInstance>()
    private val entityToInd = mutableMapOf<PointsToInstance, Int>()
    private val storesAndLoads: MutableList<Triple<Int, String, Int>> = mutableListOf()
    private val loads: MutableList<Triple<Int, String, Int>> = mutableListOf()
    private val varIndToSetOfAliases: MutableMap<Int, BitSet> = mutableMapOf()
    private val varIndToLoadSetOfAliases: MutableMap<Int, BitSet> = mutableMapOf()
    private val unknownToIds: MutableMap<String, BitSet> = mutableMapOf()
    private val aliasIdToAlias = mutableListOf<Alias>()
    private val aliasToId: Object2IntOpenHashMap<Alias> = Object2IntOpenHashMap()
    private val aliasIdToVarIds: MutableMap<Int, BitSet> = mutableMapOf()

    private fun getAliasId(alias: Alias): Int {
        if (aliasToId.containsKey(alias)) {
            return aliasToId.getInt(alias)
        }
        val id = aliasIdToAlias.size
        aliasToId.put(alias, id)
        aliasIdToAlias.add(alias)
        return id
    }

    private fun addAliasesUsingFields(forStores: Boolean) {
        var indToSetOfAliasesSize = createIndToSetOfAliasesSize(forStores)
        val correspondingMap = if (forStores) varIndToSetOfAliases else varIndToLoadSetOfAliases
        val graphRibs = if (forStores) storesAndLoads else loads
        var wasChanges = true

        var progressWhile = 0 /////
        while (wasChanges) {
            progressWhile += 1
            println("While: $progressWhile") /////
            var progressRibs = 0 /////
            var progressChanges = 0 /////
            for ((aInd, acc, bInd) in graphRibs) {
                progressRibs += 1 /////
//                if (progressRibs % 10000 == 1) {
                    println("Ribs: $progressRibs Changes: $progressChanges") /////
//                }
                val aSet = correspondingMap[aInd]!!
                for (aAliasInd in aSet.stream()) {
                    val aAlias = aliasIdToAlias[aAliasInd]
                    if (isCorrectBase(aAlias.base)) {
                        val bSynonyms = varToAliasesMap[bInd]!!
                        for (bSynInd in bSynonyms.stream()) {
                            val bSynSet = correspondingMap[bSynInd]!!
                            bSynSet.set(getAliasId(aAlias.withNewAccessor(acc)))
                            progressChanges += 1 /////
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

    private fun loadPointsToInformation(homeDirectory: String) = synchronized(this) {
        val countDirEntries = Path(homeDirectory).listDirectoryEntries().count()
        var dirId = 0
        val loadStoreIncidentVs = BitSet()
        Path(homeDirectory).listDirectoryEntries().forEach { projectDirectory ->
            (projectDirectory / "vertex_mappings.txt").bufferedReader().forEachLine { line ->
                val items = line.split("@@")
                val id = items[0].toInt() * countDirEntries + dirId
                val pti = when (items[1]) {
                    "this" -> items[2].let { PointsToInstance.This(it) }
                    "local" -> items[2].let { PointsToInstance.LocalVar(it, items[6].toInt()) }
                    "temp" -> PointsToInstance.Rubbish(id, items[4] == methodName)
                    "arg" -> items[2].let { PointsToInstance.Argument(it, items[3].toInt()) }
                    "return" -> items[2].let { PointsToInstance.ReturnValue(it) }
                    "staticcontext" -> PointsToInstance.Rubbish(id, true)
                    "staticalloc" -> PointsToInstance.Rubbish(id, false)
                    "unknown" -> PointsToInstance.Unknown(items[2], items[3])
                    "alloc" -> PointsToInstance.Rubbish(id, false)
                    else -> null
                }
                if (pti == null) {
                    println("Unsupported value of $items")
                } else if (pti.isOkWithMethod(methodName)) {
                    indToEntity[id] = pti
                    entityToInd[pti] = id
                    varToAliasesMap.put(id, BitSet().let { it.set(id); it })
                }
            }
            (projectDirectory / "results.txt").bufferedReader().forEachLine { line ->
                val (var1, var2) = line.split(" ", "\t").map { it.toInt() * countDirEntries + dirId }
                val ent1 = indToEntity[var1]
                val ent2 = indToEntity[var2]
                if (ent1 != null && ent2 != null) {
                    if (ent1 is PointsToInstance.Unknown) {
                        unknownToIds.getOrPut(ent1.stdLibMethod) { BitSet() }.set(var2)
                    } else {
                        varToAliasesMap[var1]!!.set(var2) // reversed combination must be in file
                    }
                }
            }
            (projectDirectory / "slx_result.txt.g").bufferedReader().forEachLine { line ->
                val items = line.split(" ", "\t")
                if (items[2] == "entrypoint") {
                    val var1 = items[0].toInt() * countDirEntries + dirId
                    if (indToEntity[var1] != null) {
                        indToEntity[var1] = toEntryPoint(indToEntity[var1]!!)
                        entityToInd[indToEntity[var1]!!] = var1
                    }
                }
                if (items.size == 4 && (items[2] == "store_i" || items[2] == "load_i")) { // store
                    val aInd = items[0].toInt() * countDirEntries + dirId // base
                    val bInd = items[1].toInt() * countDirEntries + dirId //.field
                    val entA = indToEntity[aInd]
                    val entB = indToEntity[bInd]
                    if (entA != null && entB != null) {
                        loadStoreIncidentVs.set(aInd)
                        loadStoreIncidentVs.set(bInd)
                        val fInd = items[3].toInt() * countDirEntries + dirId
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
            dirId += 1
        }
        for ((variable, vs) in varToAliasesMap) {
            val aliases = BitSet()
            varIndToSetOfAliases[variable] = aliases
            val redundantAliases = BitSet()
            for (v in vs.stream()) {
                val entity = indToEntity[v]!!
                if (entity is AliasBase && (isCorrectBase(entity) || loadStoreIncidentVs.get(v))) { // all is /AliasBase/, aliases only for args, rv, this or load - store ribs
                    val alias = Alias(entity, listOf())
                    val aliasId = getAliasId(alias)
                    aliasIdToVarIds.getOrPut(aliasId) { BitSet() }.set(v);
                    aliases.set(aliasId)
                } else {
                    redundantAliases.set(v)
                }
            }
            vs.andNot(redundantAliases)
            varIndToLoadSetOfAliases[variable] = aliases.clone() as BitSet
        }
        addAliasesUsingFields(false)
        for ((fromAl, toAl) in currentF2fEdges) {
            val fromId = getAliasId(fromAl)
            val toId = getAliasId(toAl)
            if (fromId != toId && aliasIdToVarIds.containsKey(fromId) && aliasIdToVarIds.containsKey(toId)) {
                for (var1 in aliasIdToVarIds[fromId]!!.stream()) {
                    for (var2 in aliasIdToVarIds[toId]!!.stream()) {
                        varToAliasesMap[var2]!!.or(varToAliasesMap[var1]!!)
                        varIndToSetOfAliases[var2]!!.or(varToAliasesMap[var1]!!)
                        val entity = indToEntity[var2]!!
                        if (entity is AliasBase && (isCorrectBase(entity) || loadStoreIncidentVs.get(var2))) { // all is /AliasBase/, aliases only for args, rv, this or load - store ribs
                            val alias = Alias(entity, listOf())
                            val aliasId = getAliasId(alias)
                            varToAliasesMap[var1]!!.set(var2)
                            aliasIdToVarIds.getOrPut(aliasId) { BitSet() }.set(var2);
                            varIndToSetOfAliases[var1]!!.set(aliasId)
                        }
                    }
                }
            }
        }
        addAliasesUsingFields(true)
    }

    data class F2FEdge(val from: Alias, val to: Alias) {
        override fun toString(): String {
            return "$from -> $to"
        }

        fun printWithMethod(): String = "${from.printWithMethod()} -> ${to.printWithMethod()}"
    }
    data class Z2FEdge(val msg: String, val to: Alias) {
        override fun toString(): String {
            return "$msg| $to"
        }

        fun printWithMethod(): String = "$msg| ${to.printWithMethod()}"
    }

    fun isCorrectBase(base: AliasBase): Boolean {
        return isCorrectStartBase(base) || base is PointsToInstance.ReturnValue
    }

    fun isCorrectStartBase(base: AliasBase): Boolean {
        return base is PointsToInstance.This || base is PointsToInstance.Argument
    }

    fun findEdges(): Pair<List<F2FEdge>, List<Z2FEdge>> {
        val f2fs = mutableSetOf<F2FEdge>()
        val z2fs = mutableSetOf<Z2FEdge>()
        for ((varInd, aliases) in varIndToSetOfAliases) {
            val fromAliases = varIndToLoadSetOfAliases[varInd]!!
            for (fromAliasId in fromAliases.stream()) {
                val fromAlias = aliasIdToAlias[fromAliasId]
                if (isCorrectStartBase(fromAlias.base)) {
                    for (toAliasId in aliases.stream()) {
                        val toAlias = aliasIdToAlias[toAliasId]
                        if (isCorrectBase(toAlias.base)
                            && toAlias.base.getMethodName() == methodName
                            && fromAlias.base.getMethodName() == methodName
                        ) {
                            f2fs.add(F2FEdge(fromAlias, toAlias))
                        }
                    }
                }
            }
        }
        for ((method, ids) in unknownToIds) {
            for (id in ids.stream()) {
                val aliases = varIndToSetOfAliases[id]
                if (aliases != null) {
                    for (toAliasId in aliases.stream()) {
                        val toAlias = aliasIdToAlias[toAliasId]
                        if (isCorrectBase(toAlias.base)) {
                            z2fs.add(Z2FEdge(method, toAlias))
                        }
                    }
                }
            }
        }
        return f2fs.toList() to z2fs.toList()
    }
}