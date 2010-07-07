package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.code_generator.*;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidCodeException;
import zinara.parser.sym;
import zinara.parser.parser;

import java.io.IOException;

public class BinaryExp extends Expression {
    public int operator;
    public Expression left;
    public Expression right;
    
    public BinaryExp (int o, Expression l, Expression r) throws TypeClashException {
	operator=o;
	left=l;
	right=r;
	type = parser.operators.check(this.operator, this.left.getType(), this.right.getType());
	if ((l.getType().getType() instanceof IntType) && (r.getType().getType() instanceof FloatType))
	    left  = new CastedExp(new FloatType(), l);
	else if ((l.getType().getType() instanceof FloatType) && (r.getType().getType() instanceof IntType))
	    right = new CastedExp(new FloatType(), r);
    }
    
    public Type getType() {
	return type;
    }

    public String toString() {
	return "("+left + " " + operator + " " + right+")" ;
    }

    public void tox86(Genx86 generate) throws IOException,InvalidCodeException {
	String save;
	String restore;

	left.register = register;
	right.register = register + 1;
	
	left.tox86(generate);

	//save
	generate.write(generate.save(register+1));

	right.tox86(generate);

	if (type instanceof IntType)
	    generate.write(intOps(generate));
	else if (type instanceof FloatType)
	    generate.write(realOps(generate));
	else{
	    System.out.println("Tipo no implementado en BinaryExp: "+type);
	    System.exit(1);
	}

	//restore
	generate.write(generate.restore(register+1));
    }

    private String intOps(Genx86 generate) throws InvalidCodeException{
	String code = "";
        String leftReg = generate.regName(left.register,left.type);
        String rightReg = generate.regName(right.register,right.type);

	if (operator == sym.PLUS){
	    code += generate.add(leftReg,rightReg);
	}
	else if (operator == sym.MINUS){
	    code += generate.sub(leftReg,rightReg);
	}
	else if (operator == sym.TIMES){
	    code += generate.imul(leftReg,rightReg);
	}
	else if (operator == sym.DIVIDE){
	    code += generate.idiv(leftReg,rightReg);
	}
	else if (operator == sym.MOD){
	    code += generate.imod(leftReg,rightReg);
	}
	else{
	    System.out.println("Operacion no implementada para enteros: "+operator);
	    System.exit(1);
	}
	
	return code;
    }

    private String realOps(Genx86 generate) throws InvalidCodeException{
	String code = "";
        String leftReg = generate.regName(left.register,left.type);
        String rightReg = generate.regName(right.register,right.type);

	if (operator == sym.PLUS){
	    code += generate.fadd(leftReg,rightReg);
	}
	else if (operator == sym.MINUS){
	    code += generate.fsub(leftReg,rightReg);
	}
	else if (operator == sym.TIMES){
	    code += generate.fmul(leftReg,rightReg);
	}
	else if (operator == sym.DIVIDE){
	    code += generate.fdiv(leftReg,rightReg);
	}
	else{
	    System.out.println("Operacion no implementada para reales: "+operator);
	    System.exit(1);
	}
	
	return code;
    }

    public boolean isStaticallyKnown() { return left.isStaticallyKnown() && right.isStaticallyKnown(); }

    public Object staticValue() {
	if (left.staticValue() instanceof Integer && right.staticValue() instanceof Integer) {
	    int leftInt  = ((Integer)left.staticValue()).intValue();
	    int rightInt = ((Integer)right.staticValue()).intValue();

	    if (operator == sym.PLUS)
		return new Integer(leftInt + rightInt);
	    else if (operator == sym.MINUS)
		return new Integer(leftInt - rightInt);
	    else if (operator == sym.TIMES)
		return new Integer(leftInt * rightInt);
	    else if (operator == sym.DIVIDE)
		return new Integer(leftInt / rightInt);
	    else if (operator == sym.MOD)
		return new Integer(leftInt % rightInt);
	} else if (left.staticValue() instanceof Float || right.staticValue() instanceof Float) {
	    float leftFloat  = ((Float)left.staticValue()).floatValue();
	    float rightFloat = ((Float)right.staticValue()).floatValue();

	    if (operator == sym.PLUS)
		return new Float(leftFloat + rightFloat);
	    else if (operator == sym.MINUS)
		return new Float(leftFloat - rightFloat);
	    else if (operator == sym.TIMES)
		return new Float(leftFloat * rightFloat);
	    else if (operator == sym.DIVIDE)
		return new Float(leftFloat / rightFloat);
	    else if (operator == sym.MOD)
		return new Float(leftFloat % rightFloat);
	} else if (left.staticValue() instanceof Integer || right.staticValue() instanceof Float) {
	    int   leftInt    = ((Integer)left.staticValue()).intValue();
	    float rightFloat = ((Float)right.staticValue()).floatValue();

	    if (operator == sym.PLUS)
		return new Float(leftInt + rightFloat);
	    else if (operator == sym.MINUS)
		return new Float(leftInt - rightFloat);
	    else if (operator == sym.TIMES)
		return new Float(leftInt * rightFloat);
	    else if (operator == sym.DIVIDE)
		return new Float(leftInt / rightFloat);
	    else if (operator == sym.MOD)
		return new Float(leftInt % rightFloat);
	} else if (left.staticValue() instanceof Float || right.staticValue() instanceof Float) {
	    float leftFloat  = ((Float)left.staticValue()).floatValue();
	    int   rightInt   = ((Integer)right.staticValue()).intValue();

	    if (operator == sym.PLUS)
		return new Float(leftFloat + rightInt);
	    else if (operator == sym.MINUS)
		return new Float(leftFloat - rightInt);
	    else if (operator == sym.TIMES)
		return new Float(leftFloat * rightInt);
	    else if (operator == sym.DIVIDE)
		return new Float(leftFloat / rightInt);
	    else if (operator == sym.MOD)
		return new Float(leftFloat % rightInt);
	}
	return null;
    }
}
