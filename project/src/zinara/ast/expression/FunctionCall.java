package zinara.ast.expression;
import zinara.code_generator.*;

import java.util.ArrayList;

import zinara.ast.type.Type;
import zinara.ast.type.FunctionType;
import zinara.symtable.SymTable;

public class FunctionCall extends Expression {
    private String name;
    private ArrayList arguments; // arraylist of ????
    private SymTable symtable;

    public FunctionCall(String name, ArrayList s, SymTable st) { 
	this.name = name;
	arguments = s;
	symtable = st;
    }

    public Type getType() {
	if (type != null) return type;
	type = ((FunctionType)symtable.getSymValueForId(this.name).getType()).getReturnType();
	return type;
    }

    public String toString() { return name + "(" + arguments + ")"; }

    public void tox86(Genx86 generate){
    }

    public boolean isStaticallyKnown() { return false; }

    public Object staticValue() { return null; };
}
