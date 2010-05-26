package zinara.ast.expression;

import zinara.code_generator.Genx86;

import java.io.IOException;

public abstract class LValue extends Expression {
    public void tox86(Genx86 generate) throws IOException {
    }
}
