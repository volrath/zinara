package zinara.ast.expression;
import zinara.code_generator.*;

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
	if (type != null) return type;
	ArrayList types = new ArrayList();
	for (int i = 0; i < value.size(); i++)
	    types.add(((Expression)value.get(0)).getType());
	type = new TupleType(types);
	return type;
    }
    // TupleType(null) = (), which in this case, doesn't exist.

    public String toString() {
	String ret = "(";
	for (int i = 0; i < value.size(); i++)
	    ret += (Expression)value.get(i) + ", ";
	return ret.substring(0, ret.length()-2) + ")";
    }

    public void tox86(Genx86 generate){
    }
}