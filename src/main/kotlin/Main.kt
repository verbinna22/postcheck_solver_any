package ru.mylogininya

fun main() {
    val (edges, markedEdges) = PointsToAdapterSingleton.getInstance().findEdges()
    SummaryChecker.checkSummaries(edges, markedEdges)
}