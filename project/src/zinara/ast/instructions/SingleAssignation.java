package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.expression.BooleanExp;
import zinara.ast.expression.Identifier;
import zinara.ast.expression.LValue;
import zinara.ast.type.BoolType;
import zinara.ast.type.IntType;
import zinara.ast.type.FloatType;
import zinara.ast.type.CharType;
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
	expr.register = register;
	lvalue.register = register + 1;
	String exprReg = generator.regName(expr.register);
	String lvalueReg = generator.regName(lvalue.register);
	if (lvalue.type.equals(new BoolType())) {
	    booleanAssignationToX86(generator);
	    return;
	}

	expr.tox86(generator);

	if (lvalue instanceof Identifier)
	    storeValue(generator,((Identifier)lvalue).currentDirection(generator), exprReg);
	else {
	    // Missing save and restore
	    lvalue.tox86(generator);
	    storeValue(generator,lvalueReg,exprReg);
	}
    }

    // This one can be improved =S
    public void booleanAssignationToX86(Genx86 generator) throws IOException {
	BooleanExp bExpr = (BooleanExp)expr;
	// if (expr instanceof LValue)
	//     ((LValue)bExpr).setAsBool(true);

	bExpr.yesLabel  = generator.newLabel();
	bExpr.noLabel   = generator.newLabel();

	bExpr.tox86(generator);
	
	generator.writeLabel(bExpr.yesLabel);
	if (lvalue instanceof Identifier)
	    generator.write(generator.movBool("["+((Identifier)lvalue).currentDirection(generator)+"]", "1"));
	else {
	    // Missing save and restore
	    lvalue.register = register;
	    lvalue.tox86(generator);
	    generator.write(generator.movBool("[" + generator.regName(lvalue.register) + "]", "1"));
	}
	generator.write(generator.jump(nextInst));

	generator.writeLabel(bExpr.noLabel);
	if (lvalue instanceof Identifier)
	    generator.write(generator.movBool("["+((Identifier)lvalue).currentDirection(generator)+"]", "0"));
	else {
	    // Missing save and restore
	    lvalue.register = register;
	    lvalue.tox86(generator);
	    generator.write(generator.movBool("[" + generator.regName(lvalue.register) + "]", "0"));
	}
    }

    private void storeValue(Genx86 generator, String lvalueReg, String exprReg)  throws IOException{
	if (lvalue.type.getType() instanceof IntType)
	    generator.write(generator.movInt("[" + lvalueReg + "]",
					     exprReg));
	else if (lvalue.type.getType() instanceof FloatType)
	    generator.write(generator.movReal("[" + lvalueReg + "]",
					      exprReg));
	else if (lvalue.type.getType() instanceof CharType)
	    generator.write(generator.movChar("[" + lvalueReg + "]",
					      exprReg));
	else
	    generator.write("asignacion de valores del tipo "+lvalue.type.getType().toString()+" no implementado\n");
    }
}
