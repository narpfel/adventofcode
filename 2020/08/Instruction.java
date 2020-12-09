public class Instruction {
    public final String mnemonic;
    public final int parameter;

    public Instruction(final String mnemonic, final int parameter) {
        this.mnemonic = mnemonic;
        this.parameter = parameter;
    }

    public static Instruction fromString(final String s) {
        final var parts = s.split(" ");
        return new Instruction(parts[0], Integer.parseInt(parts[1]));
    }
}
