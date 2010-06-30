package zinara.ast.type;

import java.util.ArrayList;

import zinara.ast.instructions.CodeBlock;

public class FunctionType extends RoutineType {
    public Type returnType;

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

    public void setName(String n) { name = n; }
    public String getName() { return name; }
}
