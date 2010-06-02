package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.code_generator.*;
import zinara.exceptions.TypeClashException;
import zinara.parser.sym;
import zinara.parser.parser;

import java.io.IOException;

public class BinaryRelationalExp extends BooleanExp {
    public int operator;
    public Expression left;
    public Expression right;
    
    public BinaryRelationalExp (int o, Expression l, Expression r) throws TypeClashException {
	operator=o;
	left=l;
	right=r;
	type = parser.operators.check(this.operator, this.left.getType(), this.right.getType());
    }
    
    public Type getType() {
	return type;
    }

    public String toString() {
	return "("+left + " " + operator + " " + right+")" ;
    }

    public void tox86(Genx86 generator) throws IOException {
	left.register  = register;
	right.register = register + 1;

	String leftReg = generator.regName(left.register);
	String rightReg = generator.regName(left.register + 1);

	// saving and restoring missing
	left.tox86(generator);
	right.tox86(generator);
	generator.write(generator.cmp(leftReg,rightReg));

	switch(operator) {
	case sym.LT:
	    lowerThan(generator, leftReg, rightReg, false);
	    break;
	case sym.GT:
	    greaterThan(generator, leftReg, rightReg, false);
	    break;
	case sym.LTE:
	    lowerThan(generator, leftReg, rightReg, true);
	    break;
	case sym.GTE:
	    greaterThan(generator, leftReg, rightReg, true);
	    break;
	case sym.SHEQ:
	    equal(generator, leftReg, rightReg, false);
	    break;
	case sym.DEEQ:
	    equal(generator, leftReg, rightReg, true);
	    break;
	case sym.NOEQ:
	    notEqual(generator, leftReg, rightReg);
	}

	generator.write(generator.jump(noLabel));
    }

    public void lowerThan(Genx86 generator, String a, String b, boolean orEqual) throws IOException {
	if (orEqual)
	    generator.write(generator.jle(yesLabel));
	else
	    generator.write(generator.jl(yesLabel));
    }

    public void greaterThan(Genx86 generator, String a, String b, boolean orEqual) throws IOException {
	if (orEqual)
	    generator.write(generator.jge(yesLabel));
	else
	    generator.write(generator.jg(yesLabel));
    }

    public void equal(Genx86 generator, String a, String b, boolean deep) throws IOException {
	generator.write(generator.je(yesLabel));
    }

    public void notEqual(Genx86 generator, String a, String b) throws IOException {
	generator.write(generator.jne(yesLabel));
    }

    public boolean isStaticallyKnown() { return left.isStaticallyKnown() && right.isStaticallyKnown(); }
}
