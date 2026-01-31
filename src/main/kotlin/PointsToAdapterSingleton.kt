package ru.mylogininya

import kotlin.io.path.Path
import kotlin.io.path.bufferedReader
import kotlin.io.path.div
import kotlin.io.path.listDirectoryEntries

class PointsToAdapterSingleton private constructor() {
    companion object {
        @Volatile
        private var instance: PointsToAdapterSingleton? = null

        fun getInstance(): PointsToAdapterSingleton {
            if (instance == null) {
                synchronized(this) {
                    if (instance == null) {
                        instance = PointsToAdapterSingleton()
                        instance!!.loadPointsToInformation("/home/nikita/process_taint_with_solver/taint_in_graph_no_field/graphs")
                    }
                }
            }
            return instance!!
        }
    }

    sealed interface AliasBase {
        fun getMethodName(): String

        fun getMethodUnifiedName(): String {
            val name = getMethodName()
            if (name.contains("<")) {
                throw IllegalStateException("must not contain <")
            }
            val methodName = name.split(")", limit=2)[1]
            return methodName.replace("#", "::").replace(", ", ",")
        }
    }

    sealed interface PointsToInstance {
        data class Rubbish(val u: Int) : PointsToInstance, AliasBase {
            override fun getMethodName(): String {
                throw IllegalStateException("must not be Rubbish")
            }
        }

        data class This(val method: String, val isEntryPoint: Boolean = false) : PointsToInstance, AliasBase {
            override fun toString(): String = "this"
            override fun getMethodName(): String = method
        }
        data class LocalVar(val method: String, val index: Int) : PointsToInstance, AliasBase {
            override fun getMethodName(): String {
                throw IllegalStateException("must not be LocalVar")
            }
        }

        data class AllocationSite(val alias: Alias, val tp: String) : PointsToInstance
        data class Argument(val method: String, val index: Int, val isEntryPoint: Boolean = false) : PointsToInstance, AliasBase {
            override fun toString(): String = "arg($index)"
            override fun getMethodName(): String = method
        }
        data class ReturnValue(val method: String, val isEntryPoint: Boolean = false) : PointsToInstance, AliasBase {
            override fun toString(): String = "return"
            override fun getMethodName(): String = method
        }
        data class Unknown(val method: String) : PointsToInstance, AliasBase {
            override fun getMethodName(): String {
                throw IllegalStateException("must not be Unknown")
            }
        }
    }

    private fun toEntryPoint(pti: PointsToInstance): PointsToInstance =
        when (pti) {
            is PointsToInstance.Argument -> PointsToInstance.Argument(pti.method, pti.index, true)
            is PointsToInstance.ReturnValue -> PointsToInstance.ReturnValue(pti.method, true)
            is PointsToInstance.This -> PointsToInstance.This(pti.method, true)
            else -> pti
        }

    private val varToAliasesMap = mutableMapOf<Int, MutableSet<Int>>()
    private val indToEntity = mutableMapOf<Int, PointsToInstance>()
    private val entityToInd = mutableMapOf<PointsToInstance, Int>()

    data class Alias(val base: AliasBase, val accessors: List<String>) {
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
    }

    fun aliasFromString(str: String): Alias {
        val elems = str.split('.')
        return Alias(aliasBaseFromString(elems[0]), elems.drop(1))
    }

    private fun aliasBaseFromString(str: String): AliasBase {
        return when {
            str == "this" -> PointsToInstance.This("")
            str == "RV" -> PointsToInstance.ReturnValue("")
            str.startsWith("arg(") -> PointsToInstance.Argument("", str.removePrefix("arg(").removeSuffix(")").toInt())
            else -> throw IllegalArgumentException("Unknown alias base")
        }
    }

    private val fIndToAccessor: MutableMap<Int, String> = mutableMapOf()
    //private val objIndToSetOfAliases: MutableMap<Int, MutableSet<Alias>> = mutableMapOf()
    private val storesAndLoads: MutableList<Triple<Set<Int>, String, Set<Int>>> = mutableListOf()
    private val loads: MutableList<Triple<Set<Int>, String, Set<Int>>> = mutableListOf()
    private val varIndToSetOfAliases: MutableMap<Int, MutableSet<Alias>> = mutableMapOf()
    private val varIndToLoadSetOfAliases: MutableMap<Int, MutableSet<Alias>> = mutableMapOf()
    private val unknownToIds: MutableMap<String, MutableSet<Int>> = mutableMapOf()

    private fun addAliasesUsingFields(forStores: Boolean) {
        var indToSetOfAliasesSize = createIndToSetOfAliasesSize(forStores)
        val correspondingMap = if (forStores) varIndToSetOfAliases else varIndToLoadSetOfAliases
        val graphRibs = if (forStores) storesAndLoads else loads
        var wasChanges = true
        while (wasChanges) {
            for ((aInds, acc, bInds) in graphRibs) {
                for (aInd in aInds) {
                    for (bInd in bInds) {
                        val bSet = correspondingMap[bInd]!!
                        val aSet = correspondingMap[aInd]!!
                        for (aAlias in aSet) {
                            bSet.add(aAlias.withNewAccessor(acc))
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
            return varIndToSetOfAliases.mapValues { value -> value.value.size }
        }
        return varIndToLoadSetOfAliases.mapValues { value -> value.value.size }
    }

    private fun findMethod(savedSignature: String): String {
        return savedSignature
    }

    private fun loadPointsToInformation(homeDirectory: String) = synchronized(this) {
        val countDirEntries = Path(homeDirectory).listDirectoryEntries().count()
        var dirId = 0
        Path(homeDirectory).listDirectoryEntries().forEach { projectDirectory ->
            (projectDirectory / "description.txt").bufferedReader().forEachLine { line ->
                val items = line.split("@")
                val pti = when (items[0]) {
                    "this" -> findMethod(items[1])?.let { PointsToInstance.This(it, true) }
                    "arg" -> findMethod(items[1])?.let { PointsToInstance.Argument(it, items[2].toInt(), true) }
                    else -> throw IllegalArgumentException("Unknown alias base")
                }
                val alias = Alias(pti as AliasBase, listOf())
                defaultEdges.add(F2FEdge(alias, alias))
            }
            (projectDirectory / "vertex_mappings.txt").bufferedReader().forEachLine { line ->
                val items = line.split("@")
                val id = items[0].toInt() * countDirEntries + dirId
                val pti = when (items[1]) {
                    "this" -> findMethod(items[2])?.let { PointsToInstance.This(it) }
                    "local" -> findMethod(items[2])?.let { PointsToInstance.LocalVar(it, items[6].toInt()) }
                    "temp" -> PointsToInstance.Rubbish(id)
                    "arg" -> findMethod(items[2])?.let { PointsToInstance.Argument(it, items[3].toInt()) }
                    "return" -> findMethod(items[2])?.let { PointsToInstance.ReturnValue(it) }
                    "staticcontext" -> PointsToInstance.Rubbish(id)
                    "staticalloc" -> PointsToInstance.Rubbish(id)
                    "unknown" -> PointsToInstance.Unknown(items[2])
                    "alloc" -> PointsToInstance.Rubbish(id)
                    else -> null
                }
                if (pti == null) {
                    println("Unsupported value of $items")
                } else {
                    indToEntity[id] = pti
                    entityToInd[pti] = id
                    varToAliasesMap.put(id, mutableSetOf(id))
                }
            }
            (projectDirectory / "results.txt").bufferedReader().forEachLine { line ->
                val (var1, var2) = line.split(" ", "\t").map { it.toInt() * countDirEntries + dirId }
                val ent1 = indToEntity[var1]!!
                if (ent1 is PointsToInstance.Unknown) {
                    unknownToIds.getOrPut(ent1.method) { mutableSetOf() }.add(var2)
                } else {
                    varToAliasesMap[var1]!!.add(var2) // reversed combination must be in file
                }
            }
            (projectDirectory / "field_mappings.txt").bufferedReader().forEachLine { line ->
                val (num, rest) = line.split("@")
                val number = num.toInt()
                fIndToAccessor[number] = if (rest == "PtArrayElementField") {
                    "[*]"
                } else {
                    val declaration = rest.split(")")[1]
                    val (cls, fieldName) = declaration.split("#")
                    fieldName
                }
            }
            (projectDirectory / "slx_result.txt.g").bufferedReader().forEachLine { line ->
                val items = line.split(" ", "\t")
                if (items[2] == "entrypoint") {
                    val var1 = items[0].toInt() * countDirEntries + dirId
                    indToEntity[var1] = toEntryPoint(indToEntity[var1]!!)
                    entityToInd[indToEntity[var1]!!] = var1
                }
                if (items.size == 4 && (items[2] == "store_i" || items[2] == "load_i")) { // store
                    val aInd = items[0].toInt() * countDirEntries + dirId // base
                    val bInd = items[1].toInt() * countDirEntries + dirId //.field
                    val fInd = items[3].toInt()
                    val acc = fIndToAccessor[fInd]!!
                    if (items[2] == "store_i") {
                        storesAndLoads.add(Triple(varToAliasesMap[aInd]!!, acc, varToAliasesMap[bInd]!!)) // a.b = c
                    } else {
                        storesAndLoads.add(Triple(varToAliasesMap[bInd]!!, acc, varToAliasesMap[aInd]!!))
                        loads.add(Triple(varToAliasesMap[bInd]!!, acc, varToAliasesMap[aInd]!!)) // c -> a.b | a, b, c
                    }
                }
            }
            dirId += 1
            fIndToAccessor.clear()
        }
        for ((variable, vs) in varToAliasesMap) {
            val aliases = mutableSetOf<Alias>()
            varIndToSetOfAliases[variable] = aliases
            for (v in vs) {
                val entity = indToEntity[v]!!
                if (entity is AliasBase) {
                    aliases.add(Alias(entity, listOf()))
                }
            }
            varIndToLoadSetOfAliases[variable] = aliases.toMutableSet()
        }
        addAliasesUsingFields(true)
        addAliasesUsingFields(false)
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

    private val defaultEdges = mutableListOf<F2FEdge>()

    fun isCorrectBase(base: PointsToAdapterSingleton.AliasBase): Boolean {
        return isCorrectStartBase(base) || base is PointsToInstance.ReturnValue && base.isEntryPoint
    }

    fun isCorrectStartBase(base: PointsToAdapterSingleton.AliasBase): Boolean {
        return base is PointsToInstance.This && base.isEntryPoint || base is PointsToInstance.Argument && base.isEntryPoint
    }

    fun findEdges(): Pair<List<F2FEdge>, List<Z2FEdge>> {
        val f2fs = mutableListOf<F2FEdge>()
        val z2fs = mutableListOf<Z2FEdge>()
        f2fs.addAll(defaultEdges)
        for ((varInd, aliases) in varIndToSetOfAliases) {
            val fromAliases = varIndToLoadSetOfAliases[varInd]!!
            for (fromAlias in fromAliases) {
                for (toAlias in aliases) {
                    if (isCorrectStartBase(fromAlias.base)
                        && isCorrectBase(toAlias.base)
                        && fromAlias.base.getMethodUnifiedName() == toAlias.base.getMethodUnifiedName()) {
                            f2fs.add(F2FEdge(fromAlias, toAlias))
                    }
                }
            }
        }
        for ((method, ids) in unknownToIds) {
            for (id in ids) {
                val aliases = varIndToSetOfAliases[id]
                if (aliases != null) {
                    for (toAlias in aliases) {
                        if (isCorrectBase(toAlias.base)) {
                            z2fs.add(Z2FEdge(method, toAlias))
                        }
                    }
                }
            }
        }
        return f2fs.toSet().toList() to z2fs.toSet().toList()
    }
}