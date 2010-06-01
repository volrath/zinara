package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.BoolType;
import zinara.code_generator.Genx86;

import java.io.IOException;

public class FalseExp extends BooleanExp {
    public FalseExp () { type = new BoolType(); }
    public Type getType() { return type; }
    public String toString() { return "False"; }

    public void tox86(Genx86 generator) throws IOException {
	generator.write(generator.jump(noLabel));
    }

    public boolean isStaticallyKnown() { return true; }
}
