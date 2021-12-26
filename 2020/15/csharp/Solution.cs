using System;
using System.Collections.Generic;
using System.Linq;

public class Solution {
    private static readonly List<int> INPUT = new List<int>{16, 12, 1, 0, 15, 7, 11};

    private static int solve(List<int> startingNumbers, int turnCount) {
        var numberToTurn = Enumerable.Repeat(-1, turnCount).ToList();
        foreach (var it in startingNumbers.SkipLast(1).Select((n, i) => new {Number = n, Index = i})) {
            numberToTurn[it.Number] = it.Index;
        }
        var lastSpoken = startingNumbers.Last();

        for (var turn = startingNumbers.Count; turn < turnCount; ++turn) {
            var lastSpokenOnTurn = numberToTurn[lastSpoken];
            numberToTurn[lastSpoken] = turn - 1;
            if (lastSpokenOnTurn < 0) {
                lastSpoken = 0;
            }
            else {
                lastSpoken = turn - lastSpokenOnTurn - 1;
            }
        };

        return lastSpoken;
    }

    public static void Main(string[] args) {
        Console.WriteLine(solve(INPUT, 2020));
        Console.WriteLine(solve(INPUT, 30_000_000));
    }
}
