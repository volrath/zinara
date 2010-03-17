package zinara.ast.expression;

import java.util.ArrayList;

import zinara.ast.type.ListType;
import zinara.ast.type.Type;

// invariant: every element of the value has the same type
public class ListExp extends Expression {
    public ArrayList value; // arraylist of expressions
    public ListExp(ArrayList v) { value = v; }
    public ListExp() { value = new ArrayList(); }

    public Type getType() { 
// 	if (value.size() > 0)
// 	    return new ListType(((Expression)value.get(0)).getType());
// 	else return new ListType(null);
	return new ListType(null); // typeclashexception handling... heavy
    }
    // ListType(null) = []

    public String toString() {
	String ret = "[";
	for (int i = 0; i < value.size(); i++)
	    ret += (Expression)value.get(i) + ", ";
	return (value.size() == 0 ? ret : ret.substring(0, ret.length()-2)) + "]";
    }
}

