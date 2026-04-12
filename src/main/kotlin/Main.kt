package ru.mylogininya

import ru.mylogininya.PointsToAdapterSingleton.Companion.homeDirectory
import kotlin.io.path.Path
import kotlin.io.path.bufferedWriter
import kotlin.io.path.div
import kotlin.io.path.listDirectoryEntries

fun main() {
    val (edges, markedEdges) = PointsToAdapterSingleton.findEdges()
    // --------
    Path(homeDirectory).listDirectoryEntries().first().also { projectDirectory ->
        (projectDirectory / "summary.txt").bufferedWriter().use { writer ->
            println("${edges.size} edges")
            edges.forEach { edge ->
                println(edge.printWithMethod())
                writer.write("${edge.printWithMethod()}\n")
            }
        }
    }
    SummaryChecker.checkSummaries(edges, markedEdges)
}