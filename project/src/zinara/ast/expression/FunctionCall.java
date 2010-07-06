package zinara.ast.expression;
import zinara.code_generator.*;

import java.util.ArrayList;
import java.io.IOException;

import zinara.ast.Param;
import zinara.ast.RoutineGenerator;
import zinara.ast.expression.Expression;
import zinara.ast.expression.Identifier;
import zinara.ast.type.Type;
import zinara.ast.type.RoutineType;
import zinara.ast.type.FunctionType;
import zinara.ast.type.ListType;
import zinara.ast.type.TupleType;
import zinara.ast.type.DictType;
import zinara.code_generator.*;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;
import zinara.symtable.*;

public class FunctionCall extends Expression {
    private String func_name;
    private ArrayList expr_list; // arraylist of expressions
    private SymTable symTable;

    public FunctionCall(String name, ArrayList s, SymTable st) { 
	this.func_name = name;
	this.expr_list = s;
	this.symTable = st;
	this.type = symTable.getSymValueForId(this.func_name).getType();
    }

    public Type getType() { return ((FunctionType)type).getReturnType(); }

    public String toString() { return func_name + "(" + expr_list + ")"; }

    public void tox86(Genx86 generator)
	throws InvalidCodeException,IOException,TypeClashException{

	RoutineGenerator.gen_routine(generator,symTable,
				     func_name,expr_list,
				     register,true);
    }

    public boolean isStaticallyKnown() { return false; }

    public Object staticValue() { return null; };
}
