package ru.mylogininya

fun main() {
    val (edges, markedEdges) = PointsToAdapterSingleton.getInstance().findEdges()
    // --------
    println("${edges.size} edges")
    edges.forEach { edge -> println(edge.printWithMethod()) }
    println("${markedEdges.size} marked edges")
    markedEdges.forEach { edge -> println(edge.printWithMethod()) }
    // --------
    SummaryChecker.checkSummaries(edges, markedEdges)
}