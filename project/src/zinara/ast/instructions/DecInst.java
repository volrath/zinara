package zinara.ast.instructions;

import zinara.ast.Declaration;

// This one is just a wrapper to make an Instruction out of a Declaration
public class DecInst extends Instruction {
    private Declaration declaration;

    public DecInst(Declaration d) { this.declaration = d; }
    public Declaration getDeclaration() { return this.declaration; }
    public void setDeclaration(Declaration d) { this.declaration = d; }
}
