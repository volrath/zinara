package zinara.ast.expression;

import zinara.ast.expression.LValue;
import zinara.ast.type.*;
import zinara.code_generator.*;
import zinara.exceptions.TypeClashException;
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
	left = l;
	right = r;
    }
    
    public Type getType() {
	return type;
    }

    public String toString() {
	return "("+left + " " + operator + " " + right+")" ;
    }

    public void tox86(Genx86 generator) throws IOException {
	//if (left instanceof LValue) ((LValue)left).setAsBool(true);
	//if (right instanceof LValue) ((LValue)right).setAsBool(true);
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
	// case sym.XOR:
	//     xorToX86(generator);
	}
    }

    public void conjuntionToX86(Genx86 generator, boolean shortCircuit) throws IOException {
	left.yesLabel  = generator.newLabel();
	left.noLabel   = (shortCircuit ? noLabel : left.yesLabel);
	
	right.yesLabel = yesLabel;
	right.noLabel  = noLabel;

	left.register  = register;
	right.register = register + 1;
	String leftReg = generator.regName(left.register);
	String rightReg = generator.regName(right.register);

	// saving and restoring register missing
	left.tox86(generator);
	if (!(left instanceof BooleanExp)){
	    generator.add(leftReg,"0");
	    generator.jz(left.noLabel);
	}

	generator.writeLabel(left.yesLabel);

	right.tox86(generator);
	if (!(right instanceof BooleanExp)){
	    generator.add(rightReg,"0");
	    generator.jz(left.noLabel);
	}
    }

    public void disjunctionToX86(Genx86 generator, boolean shortCircuit) throws IOException {
	left.noLabel   = generator.newLabel();
	left.yesLabel  = (shortCircuit ? yesLabel : left.noLabel);

	right.yesLabel = yesLabel;
	right.noLabel  = noLabel;

	left.register  = register;
	right.register = register + 1;
	String leftReg = generator.regName(left.register);
	String rightReg = generator.regName(right.register);

	// saving and restoring register missing
	left.tox86(generator);
	if (!(left instanceof BooleanExp)){
	    generator.add(leftReg,"0");
	    generator.jnz(left.yesLabel);
	}

	generator.writeLabel(left.noLabel);

	right.tox86(generator);
	if (!(right instanceof BooleanExp)){
	    generator.add(rightReg,"0");
	    generator.jnz(left.yesLabel);
	}
    }

    // public void xorToX86(Genx86 generator) throws IOException {
    // 	left.yesLabel  = yesLabel;
    // 	left.noLabel   = generator.newLabel();
    // 	right.yesLabel = yesLabel;
    // 	right.noLabel  = noLabel;

    // 	left.register  = register;
    // 	right.register = register + 1;

    // 	// saving and restoring register missing
    // 	left.tox86(generator);
    // 	generator.writeLabel(left.noLabel);
    // 	right.tox86(generator);
    // }
}
