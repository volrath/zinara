package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.code_generator.*;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidCodeException;
import zinara.parser.sym;
import zinara.parser.parser;

import java.io.IOException;

public class BinaryBooleanExp extends BooleanExp {
    public int operator;
    public Expression left;
    public Expression right;
    
    public BinaryBooleanExp (int o, Expression l, Expression r) throws TypeClashException {
	type = parser.operators.check(o, l.getType(), r.getType());
	operator=o;
	left =  l;
	right = r;
    }
    
    public Type getType() {
	return type;
    }

    public String toString() {
	return "("+left + " " + operator + " " + right+")" ;
    }

    public void tox86(Genx86 generator)
	throws IOException,InvalidCodeException,TypeClashException {
	switch(operator) {
	case sym.AND:
	    conjuntionToX86(generator, true);
	    break;
	case sym.SAND:
	    conjuntionToX86(generator, false);
	    break;
	case sym.OR:
	    disjunctionToX86(generator, true);
	    break;
	case sym.SOR:
	    disjunctionToX86(generator, false);
	    break;
	case sym.XOR:
	    xorToX86(generator);
	}
    }

    public void conjuntionToX86(Genx86 generator, boolean shortCircuit)
	throws IOException,InvalidCodeException,TypeClashException {
	left.yesLabel  = generator.newLabel();
	left.noLabel   = (shortCircuit ? noLabel : left.yesLabel);
	
	right.yesLabel = yesLabel;
	right.noLabel  = noLabel;

	left.register  = register;
	right.register = register + 1;
	String leftReg = generator.regName(left.register,left.type);
	String rightReg = generator.regName(right.register,left.type);

	left.tox86(generator);
	generator.write(generator.add(leftReg,"0"));
	generator.write(generator.jz(left.noLabel));

	generator.writeLabel(left.yesLabel);

	//save
	generator.write(generator.save(register+1));

	right.tox86(generator);
	generator.write(generator.add(rightReg,"0"));

	//restore
	generator.write(generator.restore(register+1));

	generator.write(generator.jz(left.noLabel));
    }

    public void disjunctionToX86(Genx86 generator, boolean shortCircuit)
	throws IOException,InvalidCodeException,TypeClashException{
	left.noLabel   = generator.newLabel();
	left.yesLabel  = (shortCircuit ? yesLabel : left.noLabel);

	right.yesLabel = yesLabel;
	right.noLabel  = noLabel;

	left.register  = register;
	right.register = register + 1;
	String leftReg = generator.regName(left.register,type);
	String rightReg = generator.regName(right.register,type);

	// saving and restoring register missing
	left.tox86(generator);
	generator.write(generator.add(leftReg,"0"));
	generator.write(generator.jnz(left.yesLabel));

	generator.writeLabel(left.noLabel);

	//save
	generator.write(generator.save(register+1));

	right.tox86(generator);
	generator.write(generator.add(rightReg,"0"));

	//restore
	generator.write(generator.restore(register+1));

	generator.write(generator.jnz(left.yesLabel));
    }

    public void xorToX86(Genx86 generator)
	throws IOException,InvalidCodeException,TypeClashException{
    	left.register  = register;
    	right.register = register + 1;
	String leftReg = generator.regName(left.register,type);
	String rightReg = generator.regName(right.register,type);

	//save
	generator.write(generator.save(register+1));

    	left.tox86(generator);
    	right.tox86(generator);
	generator.write(generator.xor(leftReg,rightReg));

	//restore
	generator.write(generator.restore(register+1));

	generator.write(generator.add(leftReg,"0"));
	generator.write(generator.jnz(yesLabel));
	generator.write(generator.jump(noLabel));
    }

    public boolean isStaticallyKnown() { return left.isStaticallyKnown() && right.isStaticallyKnown(); }

    public Object staticValue() {
	switch(operator) {
	case sym.AND:
	    return new Boolean(((Boolean)left.staticValue()).booleanValue() && ((Boolean)right.staticValue()).booleanValue());
	case sym.SAND:
	    return new Boolean(((Boolean)left.staticValue()).booleanValue() & ((Boolean)right.staticValue()).booleanValue());
	case sym.OR:
	    return new Boolean(((Boolean)left.staticValue()).booleanValue() || ((Boolean)right.staticValue()).booleanValue());
	case sym.SOR:
	    return new Boolean(((Boolean)left.staticValue()).booleanValue() | ((Boolean)right.staticValue()).booleanValue());
	case sym.XOR:
	    return new Boolean(((Boolean)left.staticValue()).booleanValue() ^ ((Boolean)right.staticValue()).booleanValue());
	}
	return null;
    }
}
