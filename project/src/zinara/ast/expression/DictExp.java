package zinara.ast.expression;
import zinara.code_generator.*;

import java.util.HashMap;
import java.util.Iterator;
import java.io.IOException;

import zinara.ast.type.DictType;
import zinara.ast.type.Type;
import zinara.exceptions.InvalidDictionaryException;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;

public class DictExp extends Expression {
    public HashMap value; // hashmap of string:expr

    public DictExp(HashMap v) { value = v; }
    public DictExp() { value = new HashMap(); }

    public Type getType() throws TypeClashException {
	if (type != null) return type;
	HashMap typemap = new HashMap();
	Iterator it = value.keySet().iterator();
	String ckey;
	while(it.hasNext()) {
	    ckey = (String)it.next();
	    if (typemap.put(ckey, (Type)((Expression)value.get(ckey)).getType()) != null)
		throw new TypeClashException("La clave " + ckey + " se repite en el diccionario " + this);
	}
	type = new DictType(typemap);
	return type;
    }
    // DictType(null) = {} which doesn't exist;

    public String toString() {
	String ret = "{";
	Iterator it = value.keySet().iterator();
	String ckey;
	while (it.hasNext()) {
	    ckey = (String)it.next();
	    ret += ckey + ": " + (Expression)value.get(ckey) + ", ";
	}
	return ret.substring(0, ret.length()-2) + value.size() + "}";
    }

    public void tox86(Genx86 generator)
	throws IOException, InvalidCodeException{
	Expression expr;
	//Type listType =  ((ListType)type).getInsideType();
	String reg;
	String regAddr = generator.addrRegName(register);

	Iterator it = value.keySet().iterator();
	while(it.hasNext()) {
	    //Se genera el valor
	    expr = (Expression)value.get((String)it.next());
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
	Iterator it = value.entrySet().iterator();
	while (it.hasNext()) {
	    v = (Expression)it.next();
	    isk = isk && v.isStaticallyKnown();
	}
	return isk;
    }

    public Object staticValue() {
	HashMap result = new HashMap();
	Iterator it = value.keySet().iterator();
	String ckey;
	while(it.hasNext()) {
	    ckey = (String)it.next();
	    result.put(ckey, ((Expression)value.get(ckey)).staticValue());
	}
	return result;
    }
}