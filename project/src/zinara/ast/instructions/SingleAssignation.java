package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.expression.LValue;
import zinara.code_generator.*;

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

    public String tox86(Genx86 generate) throws IOException{
	String code = "";
	int used_regs = 0;

	String lvalueDir;
	String expReg;
	
	expReg = generate.current_reg();
	code += expr.tox86(generate);

       	lvalueDir = lvalue.tox86(generate);
	//Puede que el calculo del lvalue ocupe registros o puede que no.
	//El se encarga de reservar sus registros en caso de ser necesario.

	code += generate.mov("["+lvalueDir+"]",expReg);

	//Falta: Liberar registro del lvalue si lo uso

	generate.write(code);
	generate.prevs_regs(used_regs);
	return "";
    }

    //Funcion que falta implementar.
    //Por si el calculo del lvalue ocupo un registro
    //private boolean isRegister(String)
}
