package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.code_generator.*;
import zinara.exceptions.TypeClashException;
import zinara.parser.sym;
import zinara.parser.parser;

import java.io.IOException;

public class BinaryBooleanExp extends BooleanExp {
    public int operator;
    public BooleanExp left;
    public BooleanExp right;
    
    public BinaryBooleanExp (int o, Expression l, Expression r) throws TypeClashException {
	type = parser.operators.check(o, l.getType(), r.getType());
	operator=o;
	left = (BooleanExp)l;
	right = (BooleanExp)r;
    }
    
    public Type getType() {
	return type;
    }

    public String toString() {
	return "("+left + " " + operator + " " + right+")" ;
    }

    public void tox86(Genx86 generator) throws IOException {
	switch(operator) {
	case sym.AND:
	    conjuntionToX86(generator, true);
	case sym.SAND:
	    conjuntionToX86(generator, false);
	case sym.OR:
	    disjunctionToX86(generator, true);
	case sym.SOR:
	    disjunctionToX86(generator, false);
	case sym.XOR:
	    xorToX86(generator);
	}
    }

    public void conjuntionToX86(Genx86 generator, boolean shortCircuit) throws IOException {
	BooleanExp bLeft  = (BooleanExp)left;
	BooleanExp bRight = (BooleanExp)right;

	bLeft.yesLabel  = generator.newLabel();
	bLeft.noLabel   = (shortCircuit ? noLabel : bLeft.yesLabel);
	bRight.yesLabel = yesLabel;
	bRight.noLabel  = noLabel;

	bLeft.register  = register;
	bRight.register = register + 1;

	// saving and restoring register missing
	bLeft.tox86(generator);
	generator.write(bLeft.yesLabel);
	bRight.tox86(generator);
    }

    public void disjunctionToX86(Genx86 generator, boolean shortCircuit) throws IOException {
	BooleanExp bLeft  = (BooleanExp)left;
	BooleanExp bRight = (BooleanExp)right;

	bLeft.noLabel   = generator.newLabel();
	bLeft.yesLabel  = (shortCircuit ? yesLabel : bLeft.noLabel);
	bRight.yesLabel = yesLabel;
	bRight.noLabel  = noLabel;

	bLeft.register  = register;
	bRight.register = register + 1;

	// saving and restoring register missing
	bLeft.tox86(generator);
	generator.write(bLeft.noLabel);
	bRight.tox86(generator);
    }

    public void xorToX86(Genx86 generator) throws IOException {
	BooleanExp bLeft  = (BooleanExp)left;
	BooleanExp bRight = (BooleanExp)right;

	bLeft.yesLabel  = yesLabel;
	bLeft.noLabel   = generator.newLabel();
	bRight.yesLabel = yesLabel;
	bRight.noLabel  = noLabel;

	bLeft.register  = register;
	bRight.register = register + 1;

	// saving and restoring register missing
	bLeft.tox86(generator);
	generator.write(bLeft.noLabel);
	bRight.tox86(generator);
    }
}
