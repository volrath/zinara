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
	switch(operator) {
	case sym.LT:
	    lowerThan(generator, false);
	    break;
	case sym.GT:
	    greaterThan(generator, false);
	    break;
	case sym.LTE:
	    lowerThan(generator, true);
	    break;
	case sym.GTE:
	    greaterThan(generator, true);
	    break;
	case sym.SHEQ:
	    equal(generator, false);
	    break;
	case sym.DEEQ:
	    equal(generator, true);
	    break;
	case sym.NOEQ:
	    notEqual(generator);
	}
    }

    public void lowerThan(Genx86 generator, boolean orEqual) throws IOException {
	left.register  = register;
	right.register = register + 1;

	// saving and restoring missing
	left.tox86(generator);
	right.tox86(generator);
// 	if (orEqual)
// 	    generator.write(generator.conditionalJump(generator.regName(left.register),
// 						      generator.regName(right.register),
// 						      yesLabel));
// 	else
// 	    generator.write(generator.conditionalJump(generator.regName(left.register),
// 						      generator.regName(right.register),
// 						      yesLabel));
	generator.write(generator.jump(noLabel));
    }

    public void greaterThan(Genx86 generator, boolean orEqual) throws IOException {
	left.register  = register;
	right.register = register + 1;

	// saving and restoring missing
	left.tox86(generator);
	right.tox86(generator);
// 	if (orEqual)
// 	    generator.write(generator.conditionalJump(generator.regName(right.register),
// 						      generator.regName(left.register),
// 						      yesLabel));
// 	else
// 	    generator.write(generator.conditionalJump(generator.regName(right.register),
// 						      generator.regName(left.register),
// 						      yesLabel));
	generator.write(generator.jump(noLabel));
    }

    public void equal(Genx86 generator, boolean deep) throws IOException {
	generator.write(generator.jump(yesLabel));
    }

    public void notEqual(Genx86 generator) throws IOException {
	generator.write(generator.jump(noLabel));
    }
}
