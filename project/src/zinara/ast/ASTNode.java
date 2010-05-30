package zinara.ast;

import zinara.code_generator.Genx86;

import java.io.IOException;

public abstract class ASTNode {
    public String code;
    public int register;
    public abstract void tox86(Genx86 generate) throws IOException;
}
