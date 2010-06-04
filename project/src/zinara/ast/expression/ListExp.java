package zinara.ast.expression;
import zinara.code_generator.*;

import java.util.ArrayList;

import zinara.ast.type.IntType;
import zinara.ast.type.ListType;
import zinara.ast.type.Type;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

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

    public ListExp(Expression e1, Expression e2) throws TypeClashException {
	if (!(e1.getType() instanceof IntType))
	    throw new TypeClashException("La expresion " + e1 + " debe ser del tipo <INT>");
	if (!e1.isStaticallyKnown())
	    throw new TypeClashException("La expresion " + e1 + " debe ser conocida a tiempo de compilacion");
	if (!(e2.getType() instanceof IntType))
	    throw new TypeClashException("La expresion " + e2 + " debe ser del tipo <INT>");
	if (!e2.isStaticallyKnown())
	    throw new TypeClashException("La expresion " + e2 + " debe ser conocida a tiempo de compilacion");

	Object i1 = e1.staticValue(), i2 = e2.staticValue();
	if (!(i1 instanceof Integer))
	    throw new TypeClashException("La expresion " + e1 + " no pudo ser reducida a Integer");
	if (!(i2 instanceof Integer))
	    throw new TypeClashException("La expresion " + e2 + " no pudo ser reducida a Integer");

	value = new ArrayList();
	for (int i = ((Integer)i1).intValue(); i < ((Integer)i2).intValue(); i++)
	    value.add(new IntegerExp(i));
    }

    public ListExp() { value = new ArrayList(); }

    public Type getType() throws TypeClashException { 
	if (type != null) return type;
	type = (value.size() > 0 ? new ListType(((Expression)value.get(0)).getType(), value.size()) : new ListType(null,0));
	return type;
    }

    public String toString() {
	String ret = "[";
	for (int i = 0; i < value.size(); i++)
	    ret += (Expression)value.get(i) + ", ";
	return (value.size() == 0 ? ret : ret.substring(0, ret.length()-2)) + "]";
    }

    public void tox86(Genx86 generator) throws IOException, InvalidCodeException {
	Expression expr;
	for (int i = 0; i < value.size(); i++) {
	    expr = (Expression)value.get(i);
	    expr.register = register;
	    expr.tox86(generator);
	    generator.push(generator.regName(expr.register, ((ListType)type).getInsideType()));
	}
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