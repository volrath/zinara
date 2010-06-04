package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.expression.BooleanExp;
import zinara.ast.expression.Identifier;
import zinara.ast.expression.LValue;
import zinara.ast.type.*;
import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidCodeException;

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

    public void tox86(Genx86 generator) throws IOException,InvalidCodeException {
	String exprReg;
	String lvalueReg;

	expr.register = register;
	lvalue.register = register + 1;
	if (lvalue.type.equals(new BoolType())) {
	    booleanAssignationToX86(generator);
	    return;
	}

	expr.tox86(generator);

	exprReg = generator.regName(expr.register,expr.type);
	lvalueReg = generator.addrRegName(lvalue.register);

	lvalue.currentDirection(generator);
	storeValue(generator,lvalueReg,exprReg);
    }

    // This one can be improved =S
    public void booleanAssignationToX86(Genx86 generator) throws IOException,InvalidCodeException {
	String lvalueReg;

	BooleanExp bExpr = (BooleanExp)expr;
	// if (expr instanceof LValue)
	//     ((LValue)bExpr).setAsBool(true);

	bExpr.yesLabel  = generator.newLabel();
	bExpr.noLabel   = generator.newLabel();

	//En caso de que bExpr necesite computarse
	bExpr.register = register;
	String bExprReg = generator.regName(bExpr.register,bExpr.type);

	bExpr.tox86(generator);
	if (!(bExpr instanceof BooleanExp)){
	    generator.add(bExprReg,"0");
	    generator.jz(bExpr.noLabel);
	}

	lvalue.register = register;
	lvalueReg = generator.addrRegName(lvalue.register);	

	generator.writeLabel(bExpr.yesLabel);

	// Missing save and restore
	lvalue.currentDirection(generator);
	generator.write(generator.movBool("[" + lvalueReg + "]", "1"));

	generator.write(generator.jump(nextInst));

	generator.writeLabel(bExpr.noLabel);

	// Missing save and restore
	lvalue.currentDirection(generator);
	generator.write(generator.movBool("[" + lvalueReg + "]", "0"));
    }

    private void storeValue(Genx86 generator, String lvalueReg, String exprReg)  throws IOException,InvalidCodeException{
	if (lvalue.type.getType() instanceof IntType)
	    generator.write(generator.movInt("[" + lvalueReg + "]",
					     exprReg));
	else if (lvalue.type.getType() instanceof FloatType)
	    generator.write(generator.movReal("[" + lvalueReg + "]",
					      exprReg));
	else if (lvalue.type.getType() instanceof CharType)
	    generator.write(generator.movChar("[" + lvalueReg + "]",
					      exprReg));
	else if (lvalue.type.getType() instanceof ListType) {
	    // save
	    String spAddr1 = generator.addrRegName(register + 1);
	    String spAddr2 = generator.addrRegName(register + 2);
	    for (int i = ((ListType)lvalue.type.getType()).len(); i > 0; i--) {
		generator.movAddr(spAddr1, "rsp");
		generator.movInt(spAddr2, Integer.toString(i));
		generator.imul(spAddr2, Integer.toString((i*((ListType)lvalue.type.getType()).getInsideType().size())));
		generator.add(spAddr1, spAddr2);
		storeValue(generator, lvalueReg + (i*((ListType)lvalue.type.getType()).getInsideType().size()), spAddr1);
	    }
	    // restore
	}
	else
	    throw new InvalidCodeException("asignacion a lvalues del tipo "+lvalue.type.getType()+" no implementada\n");
	    //generator.write("asignacion de valores del tipo "+lvalue.type.getType().toString()+" no implementado\n");
    }
}
