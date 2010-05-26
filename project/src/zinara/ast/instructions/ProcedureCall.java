package zinara.ast.instructions;
import zinara.code_generator.*;

import java.util.ArrayList;

import zinara.ast.expression.Expression;

public class ProcedureCall extends Instruction{
    private ArrayList expr_list; // arraylist of expressions
    private String func_name;

    public ProcedureCall(String fn, ArrayList exl){
	this.func_name = fn;
	this.expr_list = exl;
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

    public void tox86(Genx86 generate){
    }
}
