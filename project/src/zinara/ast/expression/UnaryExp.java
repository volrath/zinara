package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.code_generator.Genx86;
import zinara.parser.parser;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

public class UnaryExp extends Expression {
    public int operator;
    public Expression operand;
    
    public UnaryExp ( int o, Expression e ) throws TypeClashException { 
	operator=o;
	operand=e;
	type = parser.operators.check(this.operator, this.operand.getType(), null);
    }

    public Type getType() {
	return type;
   }

    public String toString() {
	return operator + " " + operand;
    }

    public void tox86(Genx86 generate)
	throws IOException,InvalidCodeException,TypeClashException{
	if (operand instanceof IntegerExp)
	    ((IntegerExp)operand).negative();
	else if (operand instanceof FloatExp)
	    ((FloatExp)operand).negative();
	operand.tox86(generate);
    }

    public boolean isStaticallyKnown() { return operand.isStaticallyKnown(); }

    public Object staticValue() {
	Object op = operand.staticValue();
	if (op instanceof Integer) return new Integer(-((Integer)op).intValue());
	else return new Float(-((Float)op).floatValue());
    }
}