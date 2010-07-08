package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.expression.BooleanExp;
import zinara.ast.expression.Identifier;
import zinara.ast.expression.ListExp;
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

    public void tox86(Genx86 generator)
	throws IOException,InvalidCodeException{
	String exprReg;
	String lvalueReg;

	expr.register = register;
	lvalue.register = register + 1;
	if (lvalue.type.equals(new BoolType())) {
	    booleanAssignationToX86(generator);
	    return;
	}

	//Se genera la expresion
	expr.tox86(generator);

	exprReg = generator.regName(expr.register,expr.type);
	lvalueReg = generator.addrRegName(lvalue.register);
	
	generator.save(lvalue.register);

	//Se calcula la direccion de lvalue
	lvalue.currentDirection(generator);

	//Se guarda el valor de la exp en el lvalue
	storeValue(generator, lvalue.type, 
		   lvalueReg, exprReg,
		   register+2);

	if ((expr.type.getType() instanceof ListType)&&
	    (expr instanceof ListExp)) {
	    //Si era una lista literal se genero en la pila.
	    //Hay que desempilarla
	    generator.write(generator.add(generator.stack_pointer(),
					  Integer.toString(lvalue.type.getType().size())));
	}
	
	generator.restore(lvalue.register);
    }

    // This one can be improved =S
    public void booleanAssignationToX86(Genx86 generator)
	throws IOException,InvalidCodeException{
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

	lvalue.currentDirection(generator);
	generator.write(generator.movBool("[" + lvalueReg + "]", "1"));

	generator.write(generator.jump(nextInst));

	generator.writeLabel(bExpr.noLabel);

	lvalue.currentDirection(generator);
	generator.write(generator.movBool("[" + lvalueReg + "]", "0"));
    }

    private void storeValue(Genx86 generator, Type t, 
			    String lvalueReg, String exprReg,
			    int free_register)
	throws IOException,InvalidCodeException{
	if (! (t.getType() instanceof ListType))
	    generator.write(generator.mov("[" + lvalueReg + "]",
					  exprReg, t.getType()));
	else{
	    generator.save(free_register);

	    Type listType = ((ListType)t.getType()).getInsideType();
	    String auxReg = generator.regName(free_register,listType);
	    String listTypeSize = Integer.toString(listType.size());

	    for (int i = ((ListType)t.getType()).len(); i > 0; i--) {
		generator.write(generator.mov(auxReg,"["+exprReg+"]",listType));
		generator.write(generator.mov("["+lvalueReg+"]",auxReg,listType));

		generator.write(generator.add(lvalueReg,listTypeSize));
		generator.write(generator.add(exprReg,listTypeSize));
	    }

	    generator.restore(free_register);
	}
    }
}
