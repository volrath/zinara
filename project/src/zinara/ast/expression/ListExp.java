package zinara.ast.expression;
import zinara.code_generator.*;

import java.util.ArrayList;

import zinara.ast.type.ListType;
import zinara.ast.type.Type;
import zinara.exceptions.TypeClashException;

// invariant: every element of the value has the same type
public class ListExp extends Expression {
    public ArrayList value; // arraylist of expressions
    public ListExp(ArrayList v) { value = v; }
    public ListExp() { value = new ArrayList(); }

    public Type getType() throws TypeClashException { 
	if (type != null) return type;
	type = (value.size() > 0 ? new ListType(((Expression)value.get(0)).getType(),0) : new ListType(null,0));
	return type;
	//return new ListType(null); // typeclashexception handling... heavy
    }
    // ListType(null) = []

    public String toString() {
	String ret = "[";
	for (int i = 0; i < value.size(); i++)
	    ret += (Expression)value.get(i) + ", ";
	return (value.size() == 0 ? ret : ret.substring(0, ret.length()-2)) + "]";
    }

    public void tox86(Genx86 generate){
    }

    public boolean isStaticallyKnown() {
	boolean isk = true;
	Expression v;
	for (int i = 0; i < value.size(); i++) {
	    v = (Expression)value.get(i);
	    isk = isk && v.isStaticallyKnown();
	}
	return isk;
    }
}