package zinara.ast.instructions;

import zinara.code_generator.*;

import java.io.IOException;

public abstract class Instruction {
    public abstract String toString();
    public abstract String tox86(Genx86 generate) throws IOException;
}