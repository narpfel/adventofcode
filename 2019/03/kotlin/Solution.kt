import java.io.File
import kotlin.math.absoluteValue

val directionToMove = mapOf(
    'R' to { p: Pair<Int, Int> -> p.copy(first = p.first + 1) },
    'L' to { p -> p.copy(first = p.first - 1) },
    'U' to { p -> p.copy(second = p.second + 1) },
    'D' to { p -> p.copy(second = p.second - 1) }
)

fun Pair<Int, Int>.manhattanDistance(): Int = first.absoluteValue + second.absoluteValue

fun track(s: String): Map<Pair<Int, Int>, Pair<Int, Int>> {
    var position = Pair(0, 0)
    return s.split(',').flatMap {
        val updatePosition = directionToMove.getValue(it[0])
        val length = it.drop(1).toInt()
        (0 until length).map {
            position = updatePosition(position)
            position
        }
    }
        .mapIndexed { i, p -> p to Pair(p.manhattanDistance(), i + 1) }
        .toMap()
}

fun main() {
    val tracks = File("input").readLines().map { track(it) }
    val crossings = tracks[0].keys.intersect(tracks[1].keys)
    println(crossings.map { tracks[0][it]!!.first }.min())
    println(crossings.map { tracks[0][it]!!.second + tracks[1][it]!!.second }.min())
}
