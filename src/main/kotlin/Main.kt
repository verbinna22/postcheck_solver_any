package ru.mylogininya

fun main() {
    val (edges, markedEdges) = PointsToAdapterSingleton.findEdges()
    // --------
    println("${edges.size} edges")
//    edges.forEach { edge -> println(edge.printWithMethod()) }
    println("${markedEdges.size} marked edges")
//    markedEdges.forEach { edge -> println(edge.printWithMethod()) }
    // --------
    SummaryChecker.checkSummaries(edges, markedEdges)
}