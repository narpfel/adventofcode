import java.util.ArrayList;

public final class Solution {
    final static int[] INPUT = {16, 12, 1, 0, 15, 7, 11};

    private static int solve(final int[] startingNumbers, final int turnCount) {
        final var numberToTurn = new ArrayList<Integer>(turnCount);
        for (int i = 0; i < turnCount; ++i) {
            numberToTurn.add(-1);
        }
        for (int i = 0; i < startingNumbers.length; ++i) {
            numberToTurn.set(startingNumbers[i], i);
        }
        var lastSpoken = startingNumbers[startingNumbers.length - 1];
        for (int turn = startingNumbers.length; turn < turnCount; ++turn) {
            final var lastSpokenOnTurn = numberToTurn.get(lastSpoken);
            numberToTurn.set(lastSpoken, turn - 1);
            if (lastSpokenOnTurn == -1) {
                lastSpoken = 0;
            }
            else {
                lastSpoken = turn - lastSpokenOnTurn - 1;
            }
        }
        return lastSpoken;
    }

    public static void main(String[] args) {
        System.out.println(solve(INPUT, 2020));
        System.out.println(solve(INPUT, 30000000));
    }
}
