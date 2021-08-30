import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.io.IOException;

public class Solution {
    private final static class Recipe {
        final List<Long> amountPerIngredient;
        final long score;

        Recipe(final List<Long> amountPerIngredient, final long score) {
            this.amountPerIngredient = amountPerIngredient;
            this.score = score;
        }
    }

    private static final Pattern ingredientPattern = Pattern.compile(
        "(?x)"
        + "\\w+:"
        + "\\ capacity\\ (?<capacity>-?\\d+),"
        + "\\ durability\\ (?<durability>-?\\d+),"
        + "\\ flavor\\ (?<flavor>-?\\d+),"
        + "\\ texture\\ (?<texture>-?\\d+),"
        + "\\ calories\\ (?<calories>\\d+)"
    );

    private static long score(
        final List<Long> amountPerIngredient,
        final List<List<Long>> transposedIngredients
    ) {
        var result = 1L;
        for (final var property: transposedIngredients) {
            result *= Math.max(
                0L,
                IntStream.range(0, amountPerIngredient.size())
                    .mapToLong(i -> amountPerIngredient.get(i) * property.get(i))
                    .sum()
            );
        }
        return result;
    }

    private static List<Recipe> possibleCombinations(
        final int n,
        final List<List<Long>> ingredients
    ) {
        final var transposedIngredients = transpose(ingredients);
        final var result = new ArrayList<Recipe>();
        final var values = new ArrayList<Long>();
        for (var i = 0; i < ingredients.size(); ++i) {
            values.add(0L);
        }
        outer: while (true) {
            if (values.stream().mapToLong(i -> i).sum() == 100) {
                final var amountPerIngredient = new ArrayList<Long>(values);
                result.add(new Recipe(
                    amountPerIngredient,
                    score(amountPerIngredient, transposedIngredients)
                ));
            }
            for (int i = 0, carry = 1; carry != 0 && i < values.size(); ++i) {
                final var value = values.get(i) + carry;
                carry = (int)value / n;
                values.set(i, value % n);
                if (value >= n && i == values.size() - 1) {
                    break outer;
                }
            }
        }
        return result;
    }

    private static long part1(final List<Recipe> combinations) {
        return combinations
            .stream()
            .map(recipe -> recipe.score)
            .max(Comparator.naturalOrder())
            .get();
    }

    private static long part2(
        final List<Recipe> combinations,
        final List<Long> caloriesPerIngredient
    ) {
        return combinations
            .stream()
            .filter(recipe ->
                IntStream.range(0, recipe.amountPerIngredient.size())
                .mapToLong(i -> recipe.amountPerIngredient.get(i) * caloriesPerIngredient.get(i))
                .sum()
                == 500
            )
            .map(recipe -> recipe.score)
            .max(Comparator.naturalOrder())
            .get();
    }

    private static List<List<Long>> transpose(final List<List<Long>> xss) {
        final List<List<Long>> result = new ArrayList<>();

        for (var i = 0; i < xss.size(); ++i) {
            result.add(new ArrayList<Long>());
            for (var j = 0; j < xss.get(0).size(); ++j) {
                result.get(i).add(xss.get(j).get(i));
            }
        }
        return result;
    }

    public static void main(String... args) throws IOException {
        final List<List<Long>> ingredients = new ArrayList<List<Long>>();
        final var caloriesPerIngredient = new ArrayList<Long>();
        final var input = new File("input");
        Files.lines(input.toPath())
            .forEach(line -> {
                final var match = ingredientPattern.matcher(line);
                if (!match.matches()) {
                    throw new RuntimeException(
                        String.format("input could not be parsed: `\"%s\"`", line)
                    );
                }
                final var ingredient = new ArrayList<Long>();
                ingredients.add(ingredient);
                ingredient.add(Long.parseLong(match.group("capacity")));
                ingredient.add(Long.parseLong(match.group("durability")));
                ingredient.add(Long.parseLong(match.group("flavor")));
                ingredient.add(Long.parseLong(match.group("texture")));
                caloriesPerIngredient.add(Long.parseLong(match.group("calories")));
            });

        final var combinations = possibleCombinations(100, ingredients);
        System.out.println(part1(combinations));
        System.out.println(part2(combinations, caloriesPerIngredient));
    }
}
