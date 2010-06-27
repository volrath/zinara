package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.code_generator.*;
import zinara.exceptions.InvalidCodeException;
import zinara.ast.type.RoutineType;
import zinara.symtable.*;

import java.io.IOException;
import java.util.ArrayList;

public class ProcedureCall extends Instruction{
    private ArrayList expr_list; // arraylist of expressions
    private String func_name;
    private SymTable symTable;

    public ProcedureCall(String fn, ArrayList exl, SymTable st){
	this.func_name = fn;
	this.expr_list = exl;
	this.symTable = st;
    }

    public String getFuncion(){
	return this.func_name;
    }

    public ArrayList getExpressionList(){
	return this.expr_list;
    }

    public String toString() {
	String ret = "<" + func_name + "(";
	for (int i = 0; i < expr_list.size(); i++)
	    ret += (Expression)expr_list.get(i) + ", ";
	return (ret.substring(0, ret.length()-2) + ")>");
    }

    public void tox86(Genx86 generate)
	throws InvalidCodeException,IOException{
	RoutineType routine;
	String code = "";

	code += generate.save_regs_caller(register);
	//params

	routine = (RoutineType)(symTable.getSymValueForId(func_name).type);
	code += generate.call(routine.label);
	
	//params
	code += generate.restore_regs_caller(register);

	generate.write(code);
    }
}
