package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.IntType;
import zinara.ast.type.FloatType;
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
	throws IOException,InvalidCodeException{
	String reg = generate.regName(register,operand.type);
	String stack_p = generate.stack_pointer();

	if (operand instanceof IntegerExp)
	    ((IntegerExp)operand).negative();
	else if (operand instanceof FloatExp)
	    ((FloatExp)operand).negative();

	operand.tox86(generate);

	if (operand instanceof Identifier){
	    if (operand.type instanceof IntType)
		generate.write(generate.imul(reg,"-1"));
	    else if (operand.type instanceof FloatType){
		String auxReg = generate.realRegName(register+1);

		generate.save(register+1);
		generate.write(generate.movReal(auxReg,
						generate.toReal((double)-1)));
		generate.write(generate.fmul(reg,auxReg));
		generate.restore(register+1);
	    }
	}
    }

    public boolean isStaticallyKnown() { return operand.isStaticallyKnown(); }

    public Object staticValue() {
	Object op = operand.staticValue();
	if (op instanceof Integer) return new Integer(-((Integer)op).intValue());
	else return new Float(-((Float)op).floatValue());
    }
}