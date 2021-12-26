public final class Solution {
    final static long MODULUS = 2147483647L;

    private static long lehmerRng(final long m, final long a, final long x) {
        return (a * x) % m;
    }

    private static long part1(long a, long b) {
        var result = 0L;
        for (var i = 0; i < 40_000_000; ++i) {
            a = lehmerRng(MODULUS, 16807, a);
            b = lehmerRng(MODULUS, 48271, b);
            result += ((a & 0xffff) == (b & 0xffff)) ? 1 : 0;
        }
        return result;
    }

    private static long part2(long a, long b) {
        var result = 0L;
        for (var i = 0; i < 5_000_000; ++i) {
            while (true) {
                a = lehmerRng(MODULUS, 16807, a);
                if ((a % 4) == 0) {
                    break;
                }
            }
            while (true) {
                b = lehmerRng(MODULUS, 48271, b);
                if ((b % 8) == 0) {
                    break;
                }
            }
            result += ((a & 0xffff) == (b & 0xffff)) ? 1 : 0;
        }
        return result;
    }

    public static void main(String[] args) {
        System.out.println(part1(116, 299));
        System.out.println(part2(116, 299));
    }
}
