import java.util.ArrayList;

public final class Solution {
    private static class Pair {
        public final int x;
        public final int y;

        public Pair(final int x, final int y) {
            this.x = x;
            this.y = y;
        }
    }

    final static int[] INPUT = {16, 12, 1, 0, 15, 7, 11};

    private static int solve(final int[] startingNumbers, final int turnCount) {
        final var numberToTurns = new ArrayList<Pair>(turnCount);
        for (int i = 0; i < turnCount; ++i) {
            numberToTurns.add(new Pair(-1, -1));
        }
        for (int i = 0; i < startingNumbers.length; ++i) {
            numberToTurns.set(startingNumbers[i], new Pair(i, -1));
        }
        var lastSpoken = startingNumbers[startingNumbers.length - 1];
        for (int turn = startingNumbers.length; turn < turnCount; ++turn) {
            final var p = numberToTurns.get(lastSpoken);
            if (p.y == -1) {
                lastSpoken = 0;
            }
            else {
                lastSpoken = p.x - p.y;
            }
            numberToTurns.set(lastSpoken, new Pair(turn, numberToTurns.get(lastSpoken).x));
        }
        return lastSpoken;
    }

    public static void main(String[] args) {
        System.out.println(solve(INPUT, 2020));
        System.out.println(solve(INPUT, 30000000));
    }
}
