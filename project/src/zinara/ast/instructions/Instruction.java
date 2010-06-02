package zinara.ast.instructions;

import zinara.ast.ASTNode;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

public abstract class Instruction extends ASTNode {
    public String nextInst;
    public abstract String toString();
    public abstract void tox86(Genx86 generate) throws InvalidCodeException, IOException;
}