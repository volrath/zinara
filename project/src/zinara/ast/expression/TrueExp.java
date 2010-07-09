package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.BoolType;
import zinara.code_generator.Genx86;

import java.io.IOException;

public class TrueExp extends BooleanExp {
    public TrueExp () { type = new BoolType(); }
    public Type getType() { return type; }
    public String toString() { return "True"; }

    public void tox86(Genx86 generator) throws IOException {
	String reg = generator.boolRegName(register);
	generator.write(generator.jump(yesLabel));
    }

    public boolean isStaticallyKnown() { return true; }

    public Object staticValue() { return new Boolean(true); };
}
