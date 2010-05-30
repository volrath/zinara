package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.expression.BooleanExp;
import zinara.ast.expression.Identifier;
import zinara.ast.expression.LValue;
import zinara.ast.type.BoolType;
import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

public class SingleAssignation extends Assignation {
    private LValue lvalue;
    private Expression expr;

    public boolean isSingle(){
	return true;
    }

    public SingleAssignation(LValue lv, Expression ex){
	this.lvalue = lv;
	this.expr = ex;
    }

    public LValue getLValue() {
	return this.lvalue;
    }

    public Expression getExpression(){
	return this.expr;
    }

    public String toString() {
	return "<" + lvalue + " = " +  expr + ">";
    }

    public void tox86(Genx86 generator) throws IOException {
	expr.register   = register;
	if (lvalue.type.equals(new BoolType())) {
	    booleanAssignationToX86(generator);
	    return;
	}

	expr.tox86(generator);

	if (lvalue instanceof Identifier)
	    generator.write(generator.mov(((Identifier)lvalue).currentDirection(generator), generator.regName(expr.register)));
	else {
	    // Missing save and restore
	    lvalue.register = register + 1;
	    lvalue.tox86(generator);
	    generator.write(generator.mov("[" + generator.regName(lvalue.register) + "]", generator.regName(expr.register)));
	}
    }

    // This one can be improved =S
    public void booleanAssignationToX86(Genx86 generator) throws IOException {
	BooleanExp bExpr = (BooleanExp)expr;
	if (expr instanceof LValue)
	    ((LValue)bExpr).setAsBool(true);

	bExpr.yesLabel  = generator.newLabel();
	bExpr.noLabel   = generator.newLabel();

	bExpr.tox86(generator);
	
	generator.writeLabel(bExpr.yesLabel);
	if (lvalue instanceof Identifier)
	    generator.write(generator.mov(((Identifier)lvalue).currentDirection(generator), "1"));
	else {
	    // Missing save and restore
	    lvalue.register = register;
	    lvalue.tox86(generator);
	    generator.write(generator.mov("[" + generator.regName(lvalue.register) + "]", "1"));
	}
	generator.write(generator.jump(nextInst));

	generator.writeLabel(bExpr.noLabel);
	if (lvalue instanceof Identifier)
	    generator.write(generator.mov(((Identifier)lvalue).currentDirection(generator), "0"));
	else {
	    // Missing save and restore
	    lvalue.register = register;
	    lvalue.tox86(generator);
	    generator.write(generator.mov("[" + generator.regName(lvalue.register) + "]", "0"));
	}
    }
    //Funcion que falta implementar.
    //Por si el calculo del lvalue ocupo un registro
    //private boolean isRegister(String)
}
