import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashSet;
import java.util.List;
import java.util.stream.Collectors;

public final class Solution {
    private Solution() {}

    public static void main(final String... args) throws IOException {
        final var instructions = Files.lines(Path.of("input"))
            .map(Instruction::fromString)
            .collect(Collectors.toList());
        final var result = Solution.run(instructions);
        assert(result.type == ResultType.Loop);
        System.out.println(result.result);
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
