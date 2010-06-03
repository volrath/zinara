package zinara.ast.instructions;
import zinara.code_generator.*;

import zinara.ast.Declaration;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

// This one is just a wrapper to make an Instruction out of a Declaration
public class DecInst extends Instruction {
    private Declaration declaration;

    public DecInst(Declaration d) { this.declaration = d; }
    public Declaration getDeclaration() { return this.declaration; }
    public void setDeclaration(Declaration d) { this.declaration = d; }

    public String toString() { return "<" + declaration + ">"; }

    public void tox86(Genx86 generator) throws IOException, InvalidCodeException {
	declaration.tox86(generator);
    }
}
