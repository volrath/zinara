package zinara.ast.instructions;

import zinara.ast.Param;
import zinara.ast.RoutineGenerator;
import zinara.ast.expression.Expression;
import zinara.ast.expression.Identifier;
import zinara.ast.type.Type;
import zinara.ast.type.RoutineType;
import zinara.ast.type.ListType;
import zinara.ast.type.TupleType;
import zinara.ast.type.DictType;
import zinara.code_generator.*;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;
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

    public void tox86(Genx86 generator)
	throws InvalidCodeException,IOException{
	RoutineGenerator.gen_routine(generator,symTable,
				     func_name,expr_list,
				     register,false);
    }
}
