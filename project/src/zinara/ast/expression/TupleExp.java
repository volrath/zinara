package zinara.ast.expression;
import zinara.code_generator.*;

import java.util.ArrayList;
import java.io.IOException;

import zinara.ast.type.TupleType;
import zinara.ast.type.Type;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidCodeException;

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

    public String toString() {
	String ret = "(";
	for (int i = 0; i < value.size(); i++)
	    ret += (Expression)value.get(i) + ", ";
	return ret.substring(0, ret.length()-2) + ")";
    }

    public void tox86(Genx86 generator)
	throws IOException, InvalidCodeException{
	Expression expr;
	//Type listType =  ((ListType)type).getInsideType();
	String reg;
	String regAddr = generator.addrRegName(register);

	for (int i = value.size()-1; i >= 0 ; i--) {
	    //Se genera el valor
	    expr = (Expression)value.get(i);
	    expr.register = register;
	    expr.tox86(generator);
	    
	    //Se pushea en la pila
	    reg = generator.regName(register, expr.type);
	    generator.write(generator.push(reg, expr.type.size()));
	}

	//Por ultimo, devuelvo la direccion donde comienza la lista
	generator.write(generator.mov(regAddr,generator.stack_pointer()));
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