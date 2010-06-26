package zinara.ast.type;

import java.util.ArrayList;

import zinara.ast.instructions.CodeBlock;

public class ProcedureType extends RoutineType {
    public ProcedureType(ArrayList al, CodeBlock cb) { 
	this.argsTypes = al;
	this.codeBlock = cb;
    }

    public Type getArgument(int i) {
	return (Type)argsTypes.get(i);
    }

    public int len() { return argsTypes.size(); }
    public int size() { return 0; }

    public String toString() {
	String ret = "<";
	for (int i = 0; i < argsTypes.size(); i++)
	    ret += (Type)argsTypes.get(i);
	return ret + ">";// + "{" + codeBlock + "}");
    }

    public Type getType() { return this; }

    public boolean equals(Type other) {
	return false;
    }
}
