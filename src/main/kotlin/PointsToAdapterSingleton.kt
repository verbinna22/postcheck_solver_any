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
                        instance!!.loadPointsToInformation("/mnt/data/MyOwnFolder/learning/p_algo/data/for_seqra_tests")
                    }
                }
            }
            return instance!!
        }
    }

    sealed interface AliasBase
    sealed interface PointsToInstance {
        data class Rubbish(val u: Unit) : PointsToInstance
        data class This(val method: String) : PointsToInstance, AliasBase
        data class LocalVar(val method: String, val index: Int) : PointsToInstance, AliasBase
        data class AllocationSite(val alias: Alias, val tp: String) : PointsToInstance
        data class Argument(val method: String, val index: Int) : PointsToInstance, AliasBase
        data class ReturnValue(val method: String) : PointsToInstance, AliasBase
        data class Unknown(val method: String) : PointsToInstance
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
    private val stores: MutableList<Triple<Set<Int>, String, Set<Int>>> = mutableListOf()
    private val loads: MutableList<Triple<Set<Int>, String, Set<Int>>> = mutableListOf()
    private val varIndToSetOfAliases: MutableMap<Int, MutableSet<Alias>> = mutableMapOf()
    private val varIndToLoadSetOfAliases: MutableMap<Int, MutableSet<Alias>> = mutableMapOf()
    private val unknownToIds: MutableMap<String, MutableSet<Int>> = mutableMapOf()

    private fun addAliasesUsingFields(forStores: Boolean) {
        val indToSetOfAliasesSize = createIndToSetOfAliasesSize(forStores)
        val correspondingMap = if (forStores) varIndToSetOfAliases else varIndToLoadSetOfAliases
        var wasChanges = true
        while (wasChanges) {
            for ((aInds, acc, bInds) in stores) {
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
            (projectDirectory / "vertex_mappings.txt").bufferedReader().forEachLine { line ->
                val items = line.split("@")
                val pti = when (items[1]) {
                    "this" -> findMethod(items[2])?.let { PointsToInstance.This(it) }
                    "local" -> findMethod(items[2])?.let { PointsToInstance.LocalVar(it, items[6].toInt()) }
                    "temp" -> PointsToInstance.Rubbish(Unit)
                    "arg" -> findMethod(items[2])?.let { PointsToInstance.Argument(it, items[3].toInt()) }
                    "return" -> findMethod(items[2])?.let { PointsToInstance.ReturnValue(it) }
                    "staticcontext" -> PointsToInstance.Rubbish(Unit)
                    "staticalloc" -> PointsToInstance.Rubbish(Unit)
                    "unknown" -> PointsToInstance.Unknown(items[1])
                    else -> null
                }
                if (pti == null) {
                    println("Unsupported value of $items")
                } else {
                    val id = items[0].toInt() * countDirEntries + dirId
                    indToEntity[id] = pti
                    entityToInd[pti] = id
                }
            }
            (projectDirectory / "results.txt").bufferedReader().forEachLine { line ->
                val (var1, var2) = line.split(" ", "\t").map { it.toInt() * countDirEntries + dirId }
                val ent1 = indToEntity[var1]!!
                if (ent1 is PointsToInstance.Unknown) {
                    unknownToIds.getOrPut(ent1.method) { mutableSetOf(var2) }.add(var2)
                } else {
                    varToAliasesMap.getOrPut(var1) { mutableSetOf(var1) }
                        .add(var2) // reversed combination must be in file
                }
            }
            (projectDirectory / "field_mapping.txt").bufferedReader().forEachLine { line ->
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
                val items = line.split(" ")
                if (items.size == 4 && (items[2] == "store" || items[2] == "load")) {
                    val aInd = items[0].toInt() * countDirEntries + dirId
                    val bInd = items[1].toInt() * countDirEntries + dirId
                    val fInd = items[3].toInt()
                    val acc = fIndToAccessor[fInd]!!
                    if (items[2] == "store") {
                        stores.add(Triple(varToAliasesMap[aInd]!!, acc, varToAliasesMap[bInd]!!))
                    } else {
                        loads.add(Triple(varToAliasesMap[bInd]!!, acc, varToAliasesMap[aInd]!!))
                    }
                }
            }
            dirId += 1
            fIndToAccessor.clear()
        }
        for ((variable, vs) in varToAliasesMap) {
            val aliases = mutableSetOf<Alias>()
            varIndToSetOfAliases[variable] = aliases
            varIndToLoadSetOfAliases[variable] = aliases
            for (v in vs) {
                val entity = indToEntity[v]!!
                if (entity is AliasBase) {
                    aliases.add(Alias(entity, listOf()))
                }
            }
        }
        addAliasesUsingFields(true)
        addAliasesUsingFields(false)
    }

    data class F2FEdge(val from: Alias, val to: Alias)
    data class Z2FEdge(val msg: String, val to: Alias)

    fun isCorrectBase(base: PointsToAdapterSingleton.AliasBase): Boolean {
        return base is PointsToInstance.This || base is PointsToInstance.Argument || base is PointsToInstance.ReturnValue
    }

    fun findEdges(): Pair<List<F2FEdge>, List<Z2FEdge>> {
        val f2fs = mutableListOf<F2FEdge>()
        val z2fs = mutableListOf<Z2FEdge>()
        for ((varInd, aliases) in varIndToSetOfAliases) {
            val fromAliases = varIndToLoadSetOfAliases[varInd]!!
            for (fromAlias in fromAliases) {
                for (toAlias in aliases) {
                    if (isCorrectBase(fromAlias.base) && isCorrectBase(toAlias.base)) {
                        f2fs.add(F2FEdge(fromAlias, toAlias))
                    }
                }
            }
        }
        for ((method, ids) in unknownToIds) {
            for (id in ids) {
                for (toAlias in varIndToSetOfAliases[id]!!) {
                    if (isCorrectBase(toAlias.base)) {
                        z2fs.add(Z2FEdge(method, toAlias))
                    }
                }
            }
        }
        return f2fs to z2fs
    }
}