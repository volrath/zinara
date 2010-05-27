package zinara.ast.expression;

import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

public abstract class LValue extends Expression {
    private boolean isExpression = false;

    public void setAsExpression(boolean e) { isExpression = e; }
    public boolean isExpression() { return isExpression; }

    public abstract void tox86(Genx86 generator) throws IOException;
    public void writeExpression(Genx86 generator) throws IOException {
	generator.write(generator.mov(generator.current_reg(), "[" + generator.current_reg() + "]"));
    }
}
