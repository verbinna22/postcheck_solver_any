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
    }

    private val varToObjMap = mutableMapOf<Int, MutableSet<Int>>()
    private val objToVarMap = mutableMapOf<Int, MutableSet<Int>>()
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
    private val objIndToSetOfAliases: MutableMap<Int, MutableSet<Alias>> = mutableMapOf()
    private val stores: MutableList<Triple<Set<Int>, String, Set<Int>>> = mutableListOf()

    private fun addAliasesUsingFields() {
        val indToSetOfAliasesSize = createIndToSetOfAliasesSize()
        var wasChanges = true
        while (wasChanges) {
            for ((aInds, acc, bInds) in stores) {
                for (aInd in aInds) {
                    for (bInd in bInds) {
                        val bSet = objIndToSetOfAliases[bInd]!!
                        val aSet = objIndToSetOfAliases[aInd]!!
                        for (aAlias in aSet) {
                            bSet.add(aAlias.withNewAccessor(acc))
                        }
                    }
                }
            }
            val newIndToSetOfAliasesSize = createIndToSetOfAliasesSize()
            if (indToSetOfAliasesSize == newIndToSetOfAliasesSize) {
                wasChanges = false
            }
        }
    }

    private fun createIndToSetOfAliasesSize(): Map<Int, Int> {
        return objIndToSetOfAliases.mapValues { value -> value.value.size }
    }

    private fun findMethod(savedSignature: String): String {
        return savedSignature
    }

    private fun loadPointsToInformation(homeDirectory: String) = synchronized(this) {
        val countDirEntries = Path(homeDirectory).listDirectoryEntries().count()
        var dirId = 0
        Path(homeDirectory).listDirectoryEntries().forEach { projectDirectory ->
            (projectDirectory / "results.txt").bufferedReader().forEachLine { line ->
                val (variable, obj) = line.split(" ", "\t").map { it.toInt() * countDirEntries + dirId }
                varToObjMap.getOrPut(variable) { mutableSetOf() }.add(obj)
                objToVarMap.getOrPut(obj) { mutableSetOf() }.add(variable)
            }
            (projectDirectory / "vertex_mappings.txt").bufferedReader().forEachLine { line ->
                val items = line.split("@")
                val pti = when (items[1]) {
                    "this" -> findMethod(items[2])?.let { PointsToInstance.This(it) }
                    "local" -> findMethod(items[2])?.let { PointsToInstance.LocalVar(it, items[6].toInt()) }
                    "temp" -> PointsToInstance.Rubbish(Unit)
                    "spectmp" -> PointsToInstance.Rubbish(Unit)
                    "specalloc" -> PointsToInstance.AllocationSite(aliasFromString(items[3]), items[2])
                    "arg" -> findMethod(items[2])?.let { PointsToInstance.Argument(it, items[3].toInt()) }
                    "return" -> findMethod(items[2])?.let { PointsToInstance.ReturnValue(it) }
                    "staticcontext" -> PointsToInstance.Rubbish(Unit)
                    "staticalloc" -> PointsToInstance.Rubbish(Unit)
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
            (projectDirectory / "slx_result.txt.g").bufferedReader().forEachLine { line ->
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
                val aInd = items[0].toInt() * countDirEntries + dirId
                val bInd = items[1].toInt() * countDirEntries + dirId
                val fInd = items[3].toInt()
                val acc = fIndToAccessor[fInd]!!
                stores.add(Triple(varToObjMap[aInd]!!, acc, varToObjMap[bInd]!!))
            }
            dirId += 1
            fIndToAccessor.clear()
        }
        for ((o, vs) in objToVarMap) {
            val aliases = mutableSetOf<Alias>()
            objIndToSetOfAliases[o] = aliases
            for (v in vs) {
                val entity = indToEntity[v]!!
                if (entity is AliasBase) {
                    aliases.add(Alias(entity, listOf()))
                }
            }
        }
        addAliasesUsingFields()
    }

    data class F2FEdge(val from: Alias, val to: Alias)
    data class Z2FEdge(val msg: String, val to: Alias)

    fun findEdges(): Pair<List<F2FEdge>, List<Z2FEdge>> {
        val f2fs = mutableListOf<F2FEdge>()
        val z2fs = mutableListOf<Z2FEdge>()
        for ((objInd, aliases) in objIndToSetOfAliases) {
            val alloc = (indToEntity[objInd]!! as PointsToInstance.AllocationSite)
            val fromAlias = alloc.alias
            for (toAlias in aliases) {
                if (alloc.tp == "real") {
                    f2fs.add(F2FEdge(fromAlias, toAlias))
                } else {
                    z2fs.add(Z2FEdge(alloc.tp, toAlias))
                }
            }
        }
        return f2fs to z2fs
    }
}