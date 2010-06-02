package zinara.ast.expression;
import zinara.code_generator.*;

import java.util.ArrayList;

import zinara.ast.type.ListType;
import zinara.ast.type.Type;
import zinara.exceptions.TypeClashException;

// invariant: every element of the value has the same type
public class ListExp extends Expression {
    public ArrayList value; // arraylist of expressions
    public ListExp(ArrayList v) throws TypeClashException {
	value = v;
	Type t = ((Expression)value.get(0)).getType();
	boolean consistency = true;
	for (int i = 1; i < value.size(); i++)
	    consistency = consistency && (t.equals(((Expression)value.get(i)).getType()));
	if (!consistency)
	    throw new TypeClashException("La lista " + toString() + " tiene inconsistencia de tipos");

    }
    public ListExp() { value = new ArrayList(); }

    public Type getType() throws TypeClashException { 
	if (type != null) return type;
	type = (value.size() > 0 ? new ListType(((Expression)value.get(0)).getType()) : new ListType(null));
	return type;
    }

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

    public Object staticValue() {
	ArrayList result = new ArrayList();
	for (int i = 0; i < value.size(); i++)
	    result.add(((Expression)value.get(i)).staticValue());
	return result;
    }
}