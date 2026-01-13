package ru.mylogininya

fun main() {
    val (edges, markedEdges) = PointsToAdapterSingleton.getInstance().findEdges()
    // --------
    println("${edges.size} edges")
    edges.forEach { edge -> println(edge) }
    println("${markedEdges.size} marked edges")
    markedEdges.forEach { edge -> println(edge) }
    // --------
    SummaryChecker.checkSummaries(edges, markedEdges)
}