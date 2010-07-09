package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.code_generator.*;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidCodeException;
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

    public void tox86(Genx86 generator)
	throws IOException,InvalidCodeException{
	left.register  = register;
	right.register = register + 1;

	String leftReg = generator.regName(left.register,left.type);
	String rightReg = generator.regName(left.register + 1,right.type);

	//save
	generator.write(generator.save(register+1));

	left.tox86(generator);
	right.tox86(generator);
	generator.write(generator.compare(leftReg,rightReg,left.type,right.type));

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

	//restore
	generator.write(generator.restore(register+1));
	
	generator.write(generator.jump(noLabel));
    }

    public void lowerThan(Genx86 generator, String a, String b, boolean orEqual) throws IOException,InvalidCodeException {
	if (orEqual)
	    generator.write(generator.jle(yesLabel));
	else
	    generator.write(generator.jl(yesLabel));
    }

    public void greaterThan(Genx86 generator, String a, String b, boolean orEqual) throws IOException,InvalidCodeException {
	if (orEqual)
	    generator.write(generator.jge(yesLabel));
	else
	    generator.write(generator.jg(yesLabel));
    }

    public void equal(Genx86 generator, String a, String b, boolean deep) throws IOException,InvalidCodeException {
	generator.write(generator.je(yesLabel));
    }

    public void notEqual(Genx86 generator, String a, String b) throws IOException,InvalidCodeException {
	generator.write(generator.jne(yesLabel));
    }

    public boolean isStaticallyKnown() { return left.isStaticallyKnown() && right.isStaticallyKnown(); }

    public Object staticValue() {
	Object leftO  = left.staticValue();
	Object rightO = right.staticValue();

	if (leftO instanceof Integer && rightO instanceof Integer) {
	    int leftE  = ((Integer)leftO).intValue();
	    int rightE = ((Integer)rightO).intValue();

	    switch(operator) {
	    case sym.LT:
		return new Boolean(leftE < rightE);
	    case sym.GT:
		return new Boolean(leftE > rightE);
	    case sym.LTE:
		return new Boolean(leftE <= rightE);
	    case sym.GTE:
		return new Boolean(leftE >= rightE);
	    case sym.SHEQ:
		return new Boolean(leftE == rightE);
	    case sym.DEEQ:
		return new Boolean(leftE == rightE);
	    case sym.NOEQ:
		return new Boolean(leftE != rightE);
	    }
	} else if (leftO instanceof Float && rightO instanceof Float) {
	    float leftE  = ((Float)leftO).floatValue();
	    float rightE = ((Float)rightO).floatValue();

	    switch(operator) {
	    case sym.LT:
		return new Boolean(leftE < rightE);
	    case sym.GT:
		return new Boolean(leftE > rightE);
	    case sym.LTE:
		return new Boolean(leftE <= rightE);
	    case sym.GTE:
		return new Boolean(leftE >= rightE);
	    case sym.SHEQ:
		return new Boolean(leftE == rightE);
	    case sym.DEEQ:
		return new Boolean(leftE == rightE);
	    case sym.NOEQ:
		return new Boolean(leftE != rightE);
	    }
	} else if (leftO instanceof Character && rightO instanceof Character) {
	    char leftE  = ((Character)leftO).charValue();
	    char rightE = ((Character)rightO).charValue();

	    switch(operator) {
	    case sym.LT:
		return new Boolean(leftE < rightE);
	    case sym.GT:
		return new Boolean(leftE > rightE);
	    case sym.LTE:
		return new Boolean(leftE <= rightE);
	    case sym.GTE:
		return new Boolean(leftE >= rightE);
	    case sym.SHEQ:
		return new Boolean(leftE == rightE);
	    case sym.DEEQ:
		return new Boolean(leftE == rightE);
	    case sym.NOEQ:
		return new Boolean(leftE != rightE);
	    }
	} else if (leftO instanceof Boolean && rightO instanceof Boolean) {
	    boolean leftE  = ((Boolean)leftO).booleanValue();
	    boolean rightE = ((Boolean)rightO).booleanValue();

	    switch(operator) {
	    case sym.LT:
		return new Boolean(relationalBoolean(leftE, rightE, 0));
	    case sym.GT:
		return new Boolean(relationalBoolean(leftE, rightE, 1));
	    case sym.LTE:
		return new Boolean(relationalBoolean(leftE, rightE, 2));
	    case sym.GTE:
		return new Boolean(relationalBoolean(leftE, rightE, 3));
	    case sym.SHEQ:
		return new Boolean(leftE == rightE);
	    case sym.DEEQ:
		return new Boolean(leftE == rightE);
	    case sym.NOEQ:
		return new Boolean(leftE != rightE);
	    }
	} else if (leftO instanceof Integer && rightO instanceof Float) {
	    int   leftE  = ((Integer)leftO).intValue();
	    float rightE = ((Float)rightO).floatValue();

	    switch(operator) {
	    case sym.LT:
		return new Boolean(leftE < rightE);
	    case sym.GT:
		return new Boolean(leftE > rightE);
	    case sym.LTE:
		return new Boolean(leftE <= rightE);
	    case sym.GTE:
		return new Boolean(leftE >= rightE);
	    case sym.SHEQ:
		return new Boolean(leftE == rightE);
	    case sym.DEEQ:
		return new Boolean(leftE == rightE);
	    case sym.NOEQ:
		return new Boolean(leftE != rightE);
	    }
	} else if (leftO instanceof Float && rightO instanceof Integer) {
	    float leftE  = ((Float)leftO).floatValue();
	    int   rightE = ((Integer)rightO).intValue();

	    switch(operator) {
	    case sym.LT:
		return new Boolean(leftE < rightE);
	    case sym.GT:
		return new Boolean(leftE > rightE);
	    case sym.LTE:
		return new Boolean(leftE <= rightE);
	    case sym.GTE:
		return new Boolean(leftE >= rightE);
	    case sym.SHEQ:
		return new Boolean(leftE == rightE);
	    case sym.DEEQ:
		return new Boolean(leftE == rightE);
	    case sym.NOEQ:
		return new Boolean(leftE != rightE);
	    }
	}
	return null;
    }

    public boolean relationalBoolean(boolean o1, boolean o2, int type) { return false; }
}
