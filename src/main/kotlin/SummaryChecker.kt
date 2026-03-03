package ru.mylogininya

import java.io.BufferedReader
import java.io.File
import java.util.concurrent.locks.ReentrantLock
import kotlin.concurrent.withLock
import java.io.FileWriter

class Node(
    val field: String, // field == null -> root
    val objectString: String,
    val depth: Int,
    val fieldType: String,
    val parentType: String,
    val children: MutableList<Node> = mutableListOf()
)

class MethodState(
    val thisNode: Node,
    val arguments: MutableList<Node> = mutableListOf(),
    val returnValue: Node
)

class MethodCall(
    val method: Method,
    val beforeState: MethodState,
    val afterState: MethodState
)

data class Method(
    val className: String,
    val methodName: String,
    val argsNumber: Int,
) {
    override fun toString(): String {
        return "$className::$methodName"
    }
}

sealed interface PathBase {
    data class Argument(val i: Int): PathBase {
        override fun toString(): String {
            return "arg($i)"
        }
    }

    object This: PathBase {
        override fun toString(): String {
            return "this"
        }
    }

    object RV: PathBase {
        override fun toString(): String {
            return "rv"
        }
    }
}

data class PathElem(
    val currentAccessor: String,
)

typealias PathSuffix = List<PathElem>

data class Path(
    val base: PathBase,
    val accessors: List<PathElem>,
) {
    fun withElem(elem: PathElem): Path {
        return Path(base, accessors + elem)
    }

    override fun toString(): String {
        return "$base" + accessors.joinToString("") { ".${it.currentAccessor}" }
    }
}

object SummaryChecker {
    val methodCalls = mutableMapOf<Method, MutableList<MethodCall>>()
    val lock = ReentrantLock()

    init {
        val file = File("/home/nikita/process_taint_with_solver/aspectDump.txt").bufferedReader()
        var line = file.readLine()
        val methods: Set<Pair<String, String>> = File("/home/nikita/process_taint_with_solver/taint_in_graph_no_field/funcs.txt").reader().use { file -> file.readLines() }.map { stringRepr ->
            val parts = stringRepr.split(".")
            Pair(parts.dropLast(1).joinToString("."), parts.last())
        }.toSet()
        while (line != null) {
            var before: MethodState
            var after: MethodState
            var method: Method
            if (!(line.startsWith("-"))) { throw IllegalStateException("assert") }
            line = file.readLine()
            if (!(line != null && line == "BEFORE:")) { throw IllegalStateException("assert") }
            line = file.readLine()
            if (!(line != null)) { throw IllegalStateException("assert") }
            val (className, methodName) = line.split("::")
            val (methodState, l) = parseMethodStateBefore(file)
            line = l
            before = methodState
            method = Method(className, methodName, methodState.arguments.size)
            if (!(line.startsWith("-"))) { throw IllegalStateException("assert") }
            line = file.readLine()

            if (!(line.startsWith("@"))) { throw IllegalStateException("assert") }

            line = file.readLine()
            if (!(line != null && line == "AFTER:")) { throw IllegalStateException("assert") }
            line = file.readLine()
            if (!(line != null)) { throw IllegalStateException("assert") }
            val (className2, methodName2) = line.split("::")
            val (methodState2, l2) = parseMethodStateAfter(file)
            line = l2
            if (!(Method(className, methodName, methodState2.arguments.size) == method)) { throw IllegalStateException("assert") }
            after = methodState2
            if (!(line.startsWith("@"))) { throw IllegalStateException("assert") }
            line = file.readLine()

            val methodNameWOArgs = methodName.split("(")[0]
            if (methods.contains(Pair(className, methodNameWOArgs))) {
                methodCalls.getOrPut(method) { mutableListOf() }.add(MethodCall(method, before, after))
            }
        }
    }

    private fun parseMethodStateBefore(file: BufferedReader): Pair<MethodState, String> {
        var line = file.readLine()
        val arguments: MutableList<Node> = mutableListOf()
        if (!(line == "this")) { throw IllegalStateException("assert") }
        val (thisNode, l) = parseObjectTree(file)
        line = l
        while (line.matches(Regex("\\d+"))) {
            val (argNode, l) = parseObjectTree(file)
            arguments.add(argNode)
            line = l
        }
        return Pair(MethodState(thisNode, arguments, Node("object", "0", 0, "-", "-")), line)
    }

    private fun parseMethodStateAfter(file: BufferedReader): Pair<MethodState, String> {
        var line = file.readLine()
        val arguments: MutableList<Node> = mutableListOf()
        if (!(line == "this")) { throw IllegalStateException("assert") }
        val (thisNode, l) = parseObjectTree(file)
        line = l
        while (line.matches(Regex("\\d+"))) {
            val (argNode, l) = parseObjectTree(file)
            arguments.add(argNode)
            line = l
        }
        if (!(line == "RV")) { throw IllegalStateException("assert") }
        val (rvNode, lrv) = parseObjectTree(file)
        line = lrv
        return Pair(MethodState(thisNode, arguments, rvNode), line)
    }

    private fun transformName(jvmName: String): String {
        return jvmName
        //return if (jvmName.startsWith("[")) TypeNameImpl.fromJvmName(jvmName).typeName else jvmName
    }

    private fun parseObjectTree(file: BufferedReader): Pair<Node, String> {
        val rootNodes = mutableListOf<Node>()
        val parents = mutableListOf<Node>()
        val objIdToNode = mutableMapOf<String, Node>()
        var line = file.readLine()
        if (!(line != null)) { throw IllegalStateException("assert") }
        while (
            !line.startsWith("@") &&
            !line.startsWith("-") &&
            line != "this" &&
            line != "RV" &&
            !line.matches(Regex("\\d+"))) {
            val parts = line.split(" ")
            if (!(parts.size == 6)) { throw IllegalStateException("assert") }

            val field = parts[0]
            val objectString = parts[1]
            val depth = parts[2].toInt()
            val isRepeated = parts[3]
            val parentType = transformName(parts[4])
            val fieldType = transformName(parts[5])

            val node = if (isRepeated == "repeated") {
                val node = Node(field, objectString, depth, fieldType, parentType, objIdToNode[objectString]!!.children)
                node
            } else {
                val node = Node(field, objectString, depth, fieldType, parentType)
                objIdToNode.put(objectString, node)
                node
            }
            if (depth == 0) {
                rootNodes.add(node)
                parents.clear()
                parents.add(node)
            } else {
                while (depth != parents.size) {
                    parents.removeLast()
                }
                parents.last().children.add(node)
                parents.add(node)
            }

            line = file.readLine()
            if (!(line != null)) { throw IllegalStateException("assert") }
        }
        if (!(rootNodes.size == 1)) { throw IllegalStateException("assert") }
        return Pair(rootNodes[0], line)
    }

    fun checkSummaries(edges: List<PointsToAdapterSingleton.F2FEdge>, markedEdges: List<PointsToAdapterSingleton.Z2FEdge>) = lock.withLock {
        println("CHECK SUMMARIES!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!") ////

        //----
//        val cls = classPath.findClassOrNull("org.apache.logging.log4j.message.ObjectMessage")!!
//        var mt: JIRMethod? = null
//        cls.methods.forEach { m ->
//            val name = m.name + "(" + m.parameters.joinToString(",") { it.type.typeName } + ")"
//--                println(m.name + "(" + m.parameters.joinToString(",") { it.type.typeName } + ")\n" + method.methodName) ///
//            if (name == "getFormattedMessage()") {
//                mt = m
//            }
//        }
//        val mth = mt!!
//        val instr = mth.instList.first()
//        val entryPoint = MethodEntryPoint(EmptyMethodContext, instr)
//        reportError("" + aurm.findFactToFactSummaryEdges(entryPoint, AccessPathBase.This))
//        throw IllegalArgumentException("THE END")
        ///

//        var ijk = 0 ///
        for ((method, calls) in methodCalls) {
//            if (ijk++ >= 20) {///
//                break ///
//            }///
//            if (method.className == "org.apache.logging.log4j.message.ObjectMessage") {
//                println("")
//            } ///
            if (method.toString().contains("$")) {
                throw IllegalStateException("$method")
            }
            val markedRibs = markedEdges.filter { it.to.base.getMethodUnifiedName() == method.toString() }
            val ribsList = edges.filter { it.to.base.getMethodUnifiedName() == method.toString() }
            for (call in calls) {
                processCall(call, ribsList, markedRibs)
            }
        }
    }

    private fun processCall(methodCall: MethodCall, f2fs: List<PointsToAdapterSingleton.F2FEdge>, z2fs: List<PointsToAdapterSingleton.Z2FEdge>) {
        val pathsBefore: MutableMap<String, MutableList<Path>> = mutableMapOf()
        val pathsAfter: MutableMap<String, MutableList<Path>> = mutableMapOf()
        //println("pCall: ${methodCall.beforeState.thisNode.objectString}") ///
        findAllInObject(methodCall.beforeState.thisNode, pathsBefore, PathBase.This)
        //println("pCall: ${methodCall.afterState.thisNode.objectString}") ///
        findAllInObject(methodCall.afterState.thisNode, pathsAfter, PathBase.This)
        //println("pCall: ${methodCall.beforeState.returnValue.objectString}") ///
        findAllInObject(methodCall.beforeState.returnValue, pathsBefore, PathBase.RV)
        //println("pCall: ${methodCall.afterState.returnValue.objectString}") ///
        findAllInObject(methodCall.afterState.returnValue, pathsAfter, PathBase.RV)
        var i = 0
        for (arg in methodCall.beforeState.arguments) {
            findAllInObject(arg, pathsBefore, PathBase.Argument(i))
            i += 1
        }
        i = 0
        for (arg in methodCall.afterState.arguments) {
            findAllInObject(arg, pathsAfter, PathBase.Argument(i))
            i += 1
        }
        //println("pCall: $pathsBefore $pathsAfter") ///
        for ((obj, pathsB) in pathsBefore) {
            val pathA = pathsAfter.getOrDefault(obj, mutableListOf())
            processOneObject(obj, pathsB.toSet(), pathA.toSet(), f2fs, methodCall, z2fs)
        }
    }

    private fun processOneObject(obj: String, pathsBefore: Set<Path>, pathsAfter: Set<Path>, f2fs: List<PointsToAdapterSingleton.F2FEdge>, methodCall: MethodCall, z2fs: List<PointsToAdapterSingleton.Z2FEdge>) {
        if (obj == "0") {
            return
        }
        val detectedPaths = mutableSetOf<Path>()
        for (path in pathsBefore) {
            for (edge in f2fs) {
                try {
//                    if (obj == "1077b7f7") { ///
//                        debug = true
//                    } ///
                    val suffixes: List<PathSuffix> = corresponds(path, edge.from)
                    val paths: MutableSet<Path> = mutableSetOf()
                    suffixes.forEach { suffix ->
                        paths.addAll(findCorrespondingPathsWithSuffix(edge.to, suffix))
                    }
                    detectedPaths.addAll(paths)
//                    if (obj == "1077b7f7") { ///
//                        debug = false
//                        reportError("suffixes: $suffixes paths: $paths before: $pathsBefore after: $pathsAfter $edge") ///
//                    } ///
                    for (detectedPath in paths) {
                        if (!pathsAfter.contains(detectedPath)) {
                            //-----------------------------------
//                                val pa = pathsAfter.map { it.toString() }
//                                val dp = detectedPath.toString()
//                                if (pa.contains(dp)) {
//                                    reportError("$dp <-> $pa")
//                                }
                            //------------------------------------
                            detectFalsePositive(obj, path, detectedPath, methodCall)
                        } else {
                            detectOk(obj, path, detectedPath, methodCall)
                        }
                    }
                } catch (_: UnsupportedOperationException) {
                    reportError("DETECTED UNSUPPORTED EDGE")
                }
            }
        }
        for (isPath in pathsAfter) {
            if (!detectedPaths.contains(isPath)) {
                ///-------------------------------------------
//                val pa = detectedPaths.map { it.toString() }
//                val dp = isPath.toString()
//                if (pa.contains(dp)) {
//                    reportError("$dp <-> $pa")
//                }
                //---------------------------------------------
                var isError = true
                for (zeroEdge in z2fs) {
                    val (suffixes, nativeMethod) = correspondsFinal(isPath, zeroEdge.to, zeroEdge.msg)
                    if (suffixes.isNotEmpty()) {
                        isError = false
                        detectTNBecauseOfAnalysis(obj, isPath, pathsBefore, methodCall, f2fs, detectedPaths, nativeMethod)
                    }
                }
                if (isError) {
                    detectTrueNegative(obj, isPath, pathsBefore, methodCall, f2fs, detectedPaths, z2fs)
                }
            }
        }
    }

    private fun detectTNBecauseOfAnalysis(
        obj: String,
        realPath: Path,
        pathsBefore: Set<Path>,
        methodCall: MethodCall,
        f2fs: List<PointsToAdapterSingleton.F2FEdge>,
        detectedPaths: MutableSet<Path>,
        methodName: String
    ) {
        FileWriter(fileName, true).use { writer ->
            writer.write("TN\n")//"Detected TN: $obj from ${methodCall.method} $pathsBefore is accessible with $realPath but this path wasn't detected by solver because of non-analysed method $methodName ($f2fs); detected($detectedPaths)\n")
        }
    }

    // var debug = false ///

    private const val fileName = "/home/nikita/process_taint_with_solver/analysis_stats_solver_v.txt"
    private const val errorLog = "/home/nikita/process_taint_with_solver/analysis_errors_solver_v.txt"

    private fun reportError(string: String) {
        println("$string")
        FileWriter(errorLog, true).use { writer ->
            writer.write("${string}\n")
        }
    }

    private fun detectTrueNegative(
        obj: String,
        realPath: Path,
        pathsBefore: Set<Path>,
        methodCall: MethodCall,
        f2fs: List<PointsToAdapterSingleton.F2FEdge>,
        detectedPaths: Set<Path>,
        z2fs: List<PointsToAdapterSingleton.Z2FEdge>
    ) {
        FileWriter(fileName, true).use { writer ->
            // "Detected True Negative: $obj from ${methodCall.method}\n")//
            writer.write("Detected True Negative: $obj from ${methodCall.method} $pathsBefore is accessible with $realPath but this path wasn't detected by solver ($f2fs); detected($detectedPaths); fromZero($z2fs)\n")
        }
    }

    private fun detectOk(
        obj: String,
        path: Path,
        detectedPath: Path,
        methodCall: MethodCall
    ) {
        FileWriter(fileName, true).use {  writer ->
            writer.write("ok\n")//"Detected ok: $obj from ${methodCall.method} $path could be and is with $detectedPath\n")
        }
    }

    private fun detectFalsePositive(
        obj: String,
        path: Path,
        detectedPath: Path,
        methodCall: MethodCall
    ) {
        FileWriter(fileName, true).use {  writer ->
            writer.write("False Positive\n")//""Detected False Positive: $obj from ${methodCall.method} $path could be with $detectedPath but it is not accessible\n")
        }
    }

    private fun findCorrespondingPathsWithSuffix(factAp: PointsToAdapterSingleton.Alias, suffix: PathSuffix): MutableSet<Path> {
        return when (factAp) {
//            is AccessTree -> {
//                findCorrespondingPathsSpecial(factAp, suffix)
//            }
//            is AccessGraphFinalFactAp -> {
//                findCorrespondingPathsSpecial(factAp, suffix)
//            }
            is PointsToAdapterSingleton.Alias -> {
                findCorrespondingPathsSpecial(factAp, suffix)
            }
            else -> throw IllegalArgumentException("unsupported FactApp")
        }
    }

//    private fun findCorrespondingPathsSpecial(factAp: AccessGraphFinalFactAp, suffix: PathSuffix): MutableSet<Path> {
//        val base: PathBase = transformBase(factAp.base)
//        val visitCount = 5
//        val pathsToProcess = mutableListOf<Pair<Path, Int>>(Pair(Path(base, listOf()), factAp.access.initial)) // Node marker
//        val paths = mutableSetOf<Path>()
//        val visitNodeCount = mutableMapOf<Int, Int>()
//        while (pathsToProcess.isNotEmpty()) {
//            val (path, node) = pathsToProcess.removeLast()
//            visitNodeCount.compute(node) { k, v -> if (v == null) 1 else v + 1 }
//            if (node == factAp.access.final) {
//                var p: Path? = path
//                if (!suffix.isEmpty()) {
//                    val acc = pathElemToAccessor(suffix.first())
//                    if (factAp.exclusions.contains(acc)) {
//                        p = null
//                    } else {
//                        for (elem in suffix) {
//                            p = p!!.withElem(elem)
//                        }
//                    }
//                }
//                if (p != null) {
//                    paths.add(p)
//                }
//            }
//            with(factAp.access.manager) {
//                factAp.access.stateSuccessors(node).forEach { accessor ->
//                    val nextNode = factAp.access.getStateSuccessor(node, accessor)
//                    val newPath = path.withElem(accessorToPathElem(accessor.accessor))
//                    if (visitNodeCount.getOrDefault(nextNode, 0) < visitCount) {
//                        pathsToProcess.add(Pair(newPath, nextNode))
//                    }
//                }
//            }
//        }
//        return paths
//    }

    private fun findCorrespondingPathsSpecial(factAp: PointsToAdapterSingleton.Alias, suffix: PathSuffix): MutableSet<Path> {
        val base: PathBase = transformBase(factAp.base)
        val paths = mutableSetOf<Path>()
        var accessorsNumber = 0
        val currentPath = Path(base, listOf())
        if (factAp.accessors.isNotEmpty()) {
            paths += createPathFromTree(
                factAp.accessors.first(),
                factAp.accessors.drop(1),
                currentPath,
                suffix,
                setOf()
            )
            accessorsNumber += 1
        }
        if (accessorsNumber == 0) {
            if (suffix.isEmpty()) {
                return mutableSetOf<Path>(currentPath)
            } else {
                val firstAccessor = suffix.first()
                val accessor = pathElemToAccessor (firstAccessor)
                if (false) { // factAp.exclusions.contains(accessor)
                    return mutableSetOf<Path>()
                } else {
                    var returnPath = currentPath
                    for (acc in suffix) {
                        returnPath = returnPath.withElem(acc)
                    }
                    return mutableSetOf<Path>(returnPath)
                }
            }
        }
        return paths
    }

    private fun accessorToPathElem(field: String): PathElem {
        return when (field) {
            "[*]" -> PathElem("[*]")
            else -> PathElem(field)
        }
    }

    private fun pathElemToAccessor(firstAccessor: PathElem): String {
        return firstAccessor.currentAccessor
    }

    private fun createPathFromTree(
        field: String,
        node: List<String>,
        path: Path,
        suffix: PathSuffix,
        exclusions: Set<String>
    ): MutableSet<Path> {
        val currentPath = path.withElem(accessorToPathElem(field))
        val paths = mutableSetOf<Path>()
        var accessorsNumber = 0
        if (node.isNotEmpty()) {
            accessorsNumber += 1
            paths += createPathFromTree(node.first(), node.drop(1), currentPath, suffix, exclusions)
        }
        if (accessorsNumber == 0) {
            if (suffix.isEmpty()) {
                return mutableSetOf<Path>(currentPath)
            } else {
                val firstAccessor = suffix.first()
                val accessor = pathElemToAccessor (firstAccessor)
                if (exclusions.contains(accessor)) {
                    return mutableSetOf<Path>()
                } else {
                    var returnPath = currentPath
                    for (acc in suffix) {
                        returnPath = returnPath.withElem(acc)
                    }
                    return mutableSetOf<Path>(returnPath)
                }
            }
        }
        return paths
    }

    private fun transformBase(base: PointsToAdapterSingleton.AliasBase): PathBase {
        return when (base) {
            is PointsToAdapterSingleton.PointsToInstance.Argument -> PathBase.Argument(base.index)
            is PointsToAdapterSingleton.PointsToInstance.ReturnValue -> PathBase.RV
            is PointsToAdapterSingleton.PointsToInstance.This -> PathBase.This
            else -> throw IllegalArgumentException("wrong base")
        }
    }

    private fun corresponds(
        path: Path,
        initialFactAp: PointsToAdapterSingleton.Alias
    ): List<PathSuffix> {
        if (!correspondsBase(path.base, initialFactAp.base)) {
            return listOf()
        }
        var fact = initialFactAp
        val suffixes = mutableListOf<MutableList<PathElem>>()
        var canContinue = true
        for (acc in path.accessors) {
            val realAccessor = pathElemToAccessor(acc)
//            if (debug) { ///
//                reportError("algo::: cycle begin suff: $suffixes cont: $canContinue isAbstr: ${isAbstract(fact)} fact: $fact fact after: ${fact.readAccessor(realAccessor)} $path") ///
//            } ///
            if (canContinue && isFinal(fact)) {
                if (!isInExclusions(fact, realAccessor)) { // ?
                    suffixes.add(mutableListOf<PathElem>())
                }
            }
            suffixes.forEach { suffix -> suffix.add(acc) }
            if (canContinue) {
                val rest = fact.readAccessors(realAccessor)
                if (rest == null) {
                    canContinue = false
                } else {
                    fact = rest
                }
            }
//            if (debug) { ///
//                reportError("algo::: cycle end suff: $suffixes cont: $canContinue isAbstr: ${isAbstract(fact)} fact: $fact fact after: ${fact.readAccessor(realAccessor)} $path") ///
//            } ///
        }
        val realAccessor = if (path.accessors.isEmpty()) null else pathElemToAccessor(path.accessors.last())
        if (canContinue && isFinal(fact)) {
            if (realAccessor == null || !isInExclusions(fact, realAccessor)) { // ?
                suffixes.add(mutableListOf<PathElem>())
            }
        }
//        if (debug) { ///
//            reportError("algo::: ret suff: $suffixes cont: $canContinue isAbstr: ${isAbstract(fact)} fact: $fact realAccessor: ${realAccessor == null} $path") ///
//        } ///
        return suffixes
    }

    private fun correspondsFinal(
        path: Path,
        finalFactAp: PointsToAdapterSingleton.Alias,
        mark: String
    ): Pair<List<PathSuffix>, String> {
        if (!correspondsBase(path.base, finalFactAp.base)) {
            return Pair(listOf(), "")
        }
        // reportError("--------------------------------------------------------------------------")///
        var fact = finalFactAp
        val suffixes = mutableListOf<MutableList<PathElem>>()
        var canContinue = true
        for (acc in path.accessors) {
            // reportError("suff: $suffixes cont: $canContinue final: ${isFinal(fact)} acc: $acc")///
            val realAccessor = pathElemToAccessor(acc)
            if (canContinue && isFinalF(fact)) {
                // reportError("incl: ${isInExclusions(fact, realAccessor)}")///
                if (!isInExclusionsFinal(fact, realAccessor)) {
                    suffixes.add(mutableListOf<PathElem>())
                }
            }
            suffixes.forEach { suffix -> suffix.add(acc) }
            if (canContinue) {
                val rest = fact.readAccessors(realAccessor)
                if (rest == null) {
                    canContinue = false
                } else {
                    fact = rest
                }
            }
        }
        val realAccessor = if (path.accessors.isEmpty()) null else pathElemToAccessor(path.accessors.last())
        // reportError("suff: $suffixes cont: $canContinue final: ${isFinal(fact)} realAcc: $realAccessor")///
        if (canContinue && isFinalF(fact)) {
            if (realAccessor == null || !isInExclusionsFinal(fact, realAccessor)) {
                suffixes.add(mutableListOf<PathElem>())
            }
        }
//        val mark = fact.readAccessor(AnyAccessor)!!.getStartAccessors().first { it is TaintMarkAccessor } as TaintMarkAccessor
        return Pair(suffixes, mark)
    }

    private fun isInExclusions(
        fact: PointsToAdapterSingleton.Alias,
        acc: String
    ): Boolean {
        return when (fact) {
//            is AccessGraphInitialFactAp -> fact.exclusions.contains(acc)
//            is AccessPath -> fact.exclusions.contains(acc)
//            is AccessPathWithCycles -> fact.exclusions.contains(acc)
            is PointsToAdapterSingleton.Alias -> false
            else -> throw IllegalArgumentException("this fact type is unsupported")
        }
    }

    private fun isInExclusionsFinal(
        fact: PointsToAdapterSingleton.Alias,
        acc: String
    ): Boolean {
        return when (fact) {
            is PointsToAdapterSingleton.Alias -> false
            else -> throw IllegalArgumentException("this fact type is unsupported")
        }
    }

    private fun isFinal(fact: PointsToAdapterSingleton.Alias): Boolean {
        return fact.accessors.isEmpty()
    }

    private fun isFinalF(fact: PointsToAdapterSingleton.Alias): Boolean {
        return fact.accessors.isEmpty()
    }

    private fun correspondsBase(
        base: PathBase,
        baseAp: PointsToAdapterSingleton.AliasBase
    ): Boolean {
        return when (base) {
            is PathBase.Argument -> baseAp is PointsToAdapterSingleton.PointsToInstance.Argument && baseAp.index == base.i
            PathBase.RV -> baseAp is PointsToAdapterSingleton.PointsToInstance.ReturnValue
            PathBase.This -> baseAp is PointsToAdapterSingleton.PointsToInstance.This
        }
    }

    private fun findAllInObject(obj: Node, paths: MutableMap<String, MutableList<Path>>, base: PathBase) {
//        println("Algo before: ${paths} obj: ${obj.objectString} base: ${base}") ///
        val visitCount = mutableMapOf<String, Int>()
        val queue = ArrayDeque<Pair<Node, Path>>()
        queue.add(Pair(obj, Path(base, mutableListOf())))
        while (!queue.isEmpty()) {
            val (current, path) = queue.removeLast()
            paths.getOrPut(current.objectString) { mutableListOf() }.add(path)
            visitCount.compute(current.objectString) { _, oldValue ->
                (oldValue ?: 0) + 1
            }
//            println("Algo: ${paths} current: ${current.objectString}") ///
            for (child in current.children) {
                if (visitCount.getOrPut(child.objectString) { 0 } <= 5) {
                    val accessor = if (child.field[0] == '[') PathElem("[*]") else PathElem(child.field)
                    val newPath = path.withElem(accessor) // PathElem(child.parentType, accessor, child.fieldType)
                    queue.add(Pair(child, newPath))
                }
            }
        }
    }
}