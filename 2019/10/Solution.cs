using System;
using System.Linq;
using System.IO;
using System.Collections.Generic;


public class Solution {
    public static int Gcd(int x, int y) {
        x = Math.Abs(x);
        y = Math.Abs(y);
        while (y != 0) {
            (x, y) = (y, x % y);
        }
        return x;
    }

    public static void Main(string[] args) {
        var input = File.ReadAllText("input")
            .Split(new Char[]{'\n'})
            .SelectMany((line, y) => line.Select((c, x) => new {X = x, Y = y, C = c}))
            .Where(a => a.C == '#')
            .Select(a => new {X = a.X, Y = a.Y})
            .ToList();

        var asteroids = input.Select(asteroid =>
            input
            .Where(a => a != asteroid)
            .Select(a => {
                var x = a.X - asteroid.X;
                var y = a.Y - asteroid.Y;
                var gcd = Gcd(x, y);
                return new {
                    Direction = new { X = x / gcd, Y = y / gcd },
                    Offset = new { X = x, Y = y },
                    Point = a
                };
            })
            .ToList()
        )
            .Select(list => (list.Select(x => x.Direction).Distinct().Count(), list.Count, list))
            .ToList();

        // FIXME: For some reason, `Enumerable.Max` doesn’t take a key function,
        // so the complete `List` has to be sorted, because for some stupid reason
        // `List` is not sortable. Ugh.
        asteroids.Sort((x, y) => (x.Item1, x.Item2).CompareTo((y.Item1, y.Item2)));

        var solution = asteroids.Last();

        Console.WriteLine(solution.Item1);
        var part2 = solution
            .Item3
            .OrderByDescending(a => Math.Atan2(a.Direction.X, a.Direction.Y))
            .GroupBy(a => a.Direction)
            .SelectMany(xs =>
                xs.Select((x, i) => new {
                    Direction = x.Direction,
                    Offset = x.Offset,
                    Point = x.Point,
                    Index = i
                })
            )
            .OrderBy(a => (a.Index, -Math.Atan2(a.Direction.X, a.Direction.Y)))
            .Skip(199)
            .First()
            .Point;
        Console.WriteLine(100 * part2.X + part2.Y);
    }
}
