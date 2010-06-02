package zinara.ast.expression;

import zinara.ast.expression.BooleanExp;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

public abstract class LValue extends Expression {
    // public void setAsBool(boolean b) { isBool = b; }
    // public boolean isBool() { return isBool; }

    // public void setAsExpression(boolean e) { isExpression = e; }
    // public boolean isExpression() { return isExpression; }

    public abstract void tox86(Genx86 generator) throws IOException, InvalidCodeException;

    public abstract void currentDirection(Genx86 generator) throws IOException, InvalidCodeException;

    // public void writeExpression(Genx86 generator) throws IOException {
    // 	generator.write(generator.mov(generator.regName(register), "[" + generator.regName(register) + "]"));
    // }

    // public void writeBooleanExpression(Genx86 generator) throws IOException {
    // 	// This should do a conditional jump on wether the reg value
    // 	// is 1 (jump to yesLabel) or 0 (jump to noLabel)
    // 	//generator.write(generator.ifEqualJump(generator.regName(register), "0", noLabel));
    // 	generator.write("lvalue " + this + " is going to " + generator.jump(yesLabel));
    // }
}
