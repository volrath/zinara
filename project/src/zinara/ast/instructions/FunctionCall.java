package zinara.ast.instructions;

import java.util.ArrayList;

public class FunctionCall extends Instruction{
    private ArrayList expr_list; // arraylist of expressions
    private String func_name;

    public FunctionCall(String fn, ArrayList exl){
	this.func_name = fn;
	this.expr_list = exl;
    }

    public String getFuncion(){
	return this.func_name;
    }

    public ArrayList getExpressionList(){
	return this.expr_list;
    }
}
