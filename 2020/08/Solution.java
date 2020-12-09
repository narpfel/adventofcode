import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashSet;
import java.util.List;
import java.util.ArrayList;
import java.util.stream.IntStream;
import java.util.stream.Collectors;

public final class Solution {
    private Solution() {}

    public static void main(final String... args) throws IOException {
        final var instructions = Files.lines(Path.of("input"))
            .map(Instruction::fromString)
            .collect(Collectors.toList());
        System.out.println(part1(instructions));
        System.out.println(part2(instructions));
    }

    private static int part1(final List<Instruction> instructions) {
        final var result = Solution.run(instructions);
        assert(result.type == ResultType.Loop);
        return result.result;
    }

    private static int part2(final List<Instruction> instructions) {
        return IntStream.range(0, instructions.size())
            .filter(i -> instructions.get(i).mnemonic != "acc")
            .mapToObj(i -> {
                final Instruction instruction = Solution.replace(instructions.get(i));
                final var newInstructions = new ArrayList<Instruction>(instructions);
                newInstructions.set(i, instruction);
                return newInstructions;
            })
            .map(newInstructions -> Solution.run(newInstructions))
            .filter(result -> result.type == ResultType.Ended)
            .mapToInt(result -> result.result)
            .findFirst()
            .getAsInt();
    }

    private static Instruction replace(final Instruction instruction) {
        if (instruction.mnemonic == "nop") {
            return new Instruction("jmp", instruction.parameter);
        }
        else {
            return new Instruction("nop", instruction.parameter);
        }
    }

    private static Result run(final List<Instruction> instructions) {
        var programCounter = 0;
        var accumulator = 0;
        final var executedInstructions = new HashSet<Integer>();

        while (true) {
            if (executedInstructions.contains(programCounter)) {
                return new Result(ResultType.Loop, accumulator);
            }
            executedInstructions.add(programCounter);
            if (programCounter == instructions.size()) {
                return new Result(ResultType.Ended, accumulator);
            }
            else if (programCounter > instructions.size()) {
                return new Result(ResultType.Invalid, -1);
            }
            final var instruction = instructions.get(programCounter);
            switch (instruction.mnemonic) {
                case "nop":
                    break;
                case "acc":
                    accumulator += instruction.parameter;
                    break;
                case "jmp":
                    programCounter += instruction.parameter - 1;
                    break;
            }
            programCounter += 1;
        }
    }
}
