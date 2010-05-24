package zinara.ast.type;

import java.util.ArrayList;

import zinara.ast.instructions.CodeBlock;

public class ProcedureType extends Type {
    public ArrayList argsTypes; // arraylist of Type
    public CodeBlock codeBlock;

    public ProcedureType(ArrayList al, CodeBlock cb) { 
	this.argsTypes = al;
	this.codeBlock = cb;
    }

    public Type getArgument(int i) {
	return (Type)argsTypes.get(i);
    }

    public int size() { return argsTypes.size(); }

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
