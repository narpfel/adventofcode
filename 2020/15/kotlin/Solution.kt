val INPUT = arrayOf(16, 12, 1, 0, 15, 7, 11)

fun solve(startingNumbers: Array<Int>, turnCount: Int): Int {
    val numberToTurn = IntArray(turnCount) { _ -> -1 }
    startingNumbers.dropLast(1).forEachIndexed { i, n ->
        numberToTurn[n] = i
    }
    var lastSpoken = startingNumbers.last()

    (startingNumbers.size until turnCount).forEach { turn ->
        val lastSpokenOnTurn = numberToTurn[lastSpoken]
        numberToTurn[lastSpoken] = turn - 1
        if (lastSpokenOnTurn < 0) {
            lastSpoken = 0
        }
        else {
            lastSpoken = turn - lastSpokenOnTurn - 1
        }
    }

    return lastSpoken
}

fun main() {
    println(solve(INPUT, 2020))
    println(solve(INPUT, 30_000_000))
}
