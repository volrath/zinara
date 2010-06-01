package zinara.ast.expression;

import zinara.ast.expression.BooleanExp;
import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

public abstract class LValue extends BooleanExp {
    boolean isBool, isExpression;

    public void setAsBool(boolean b) { isBool = b; }
    public boolean isBool() { return isBool; }

    public void setAsExpression(boolean e) { isExpression = e; }
    public boolean isExpression() { return isExpression; }

    public abstract void tox86(Genx86 generator) throws IOException;
    public abstract void writeExpression(Genx86 generator) throws IOException;
  
    public void writeBooleanExpression(Genx86 generator) throws IOException {
	generator.add(generator.regName(register), "0");
    	generator.write(generator.jz(noLabel));
	generator.write(generator.jump(yesLabel));
    }
}
