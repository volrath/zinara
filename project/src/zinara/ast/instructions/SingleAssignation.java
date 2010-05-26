package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.expression.Identifier;
import zinara.ast.expression.LValue;
import zinara.exceptions.TypeClashException;
import zinara.code_generator.Genx86;

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
	String code = "";
	int used_regs = 0;

	String lvalueDir;
	String expReg;
	
	expReg = generator.current_reg();
	expr.tox86(generator);

	//Puede que el calculo del lvalue ocupe registros o puede que no.
	//El se encarga de reservar sus registros en caso de ser necesario.
	if (lvalue instanceof Identifier)
	    generator.write(generator.mov("["+ ((Identifier)lvalue).currentDirection(generator) +"]", expReg));
	else {
	    generator.next_reg();
	    lvalue.tox86(generator);
	    generator.prevs_regs(1);
	}
    }

    //Funcion que falta implementar.
    //Por si el calculo del lvalue ocupo un registro
    //private boolean isRegister(String)
}
