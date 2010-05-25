package zinara.ast.instructions;

import zinara.ast.ASTNode;
import zinara.code_generator.Genx86;

import java.io.IOException;

public abstract class Instruction extends ASTNode {
    public abstract String toString();
    public abstract String tox86(Genx86 generate) throws IOException;
}