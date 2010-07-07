package zinara.ast.type;

import java.util.ArrayList;

import zinara.ast.Param;
import zinara.ast.instructions.CodeBlock;

public abstract class RoutineType extends Type {
    public ArrayList args; // arraylist of Param
    public CodeBlock codeBlock;
    public String label;

    public int len() { return args.size(); }

    public Param getArgument(int i) {
	return ((Param)(args.get(i)));
    }

    public Type getArgumentType(int i) {
	return ((Param)(args.get(i))).getType();
    }

    public String toString() {
	String ret = "<";
	for (int i = 0; i < args.size(); i++)
	    ret += ((Param)(args.get(i))).getType();
	return ret + ">";// + "{" + codeBlock + "}");
    }
}
