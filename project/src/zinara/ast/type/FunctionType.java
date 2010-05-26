package zinara.ast.type;

import java.util.ArrayList;

import zinara.ast.instructions.CodeBlock;

public class FunctionType extends Type {
    public ArrayList argsTypes; // arraylist of Type
    public Type returnType;
    public CodeBlock codeBlock;

    public FunctionType(ArrayList al, Type rt, CodeBlock cb) { 
	this.argsTypes = al;
	this.returnType = rt;
	this.codeBlock = cb;
    }

    public Type getArgument(int i) {
	return (Type)argsTypes.get(i);
    }

    public Type getReturnType() { return returnType; }

    public int len() { return argsTypes.size(); }

    public int size() { return 0; }

    public String toString() {
	String ret = "<";
	for (int i = 0; i < argsTypes.size(); i++)
	    ret += (Type)argsTypes.get(i) + "->";
	return (ret + returnType) + ">";// + "{" + codeBlock + "}");
    }

    public Type getType() { return this; }

    public boolean equals(Type other) {
	if (!(other instanceof FunctionType)) return false;
	FunctionType otherFunction = (FunctionType)other;
	if (size() != otherFunction.size()) return false;
	for (int i = 0; i < size(); i++)
	    if (!getArgument(i).equals(otherFunction.getArgument(i))) return false;
	return returnType.equals(otherFunction.getReturnType());
    }
}
