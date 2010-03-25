package zinara.ast.expression;

import java.util.ArrayList;

import zinara.ast.type.TupleType;
import zinara.ast.type.Type;
import zinara.exceptions.TypeClashException;

// invariant: value is at least 2 long
public class TupleExp extends Expression {
    public ArrayList value; // arraylist of expressions

    public TupleExp(ArrayList v) { value = v; }
    public TupleExp() { value = new ArrayList(); }

    public Type getType() throws TypeClashException { 
	ArrayList types = new ArrayList();
	for (int i = 0; i < value.size(); i++)
	    types.add(((Expression)value.get(0)).getType());
	return new TupleType(types);
	//return new TupleType(null); // typeclashexception handling... heavy
    }
    // TupleType(null) = (), which in this case, doesn't exist.

    public String toString() {
	String ret = "(";
	for (int i = 0; i < value.size(); i++)
	    ret += (Expression)value.get(i) + ", ";
	return ret.substring(0, ret.length()-2) + ")";
    }
}