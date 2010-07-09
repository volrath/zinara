package zinara.ast.expression;
import zinara.code_generator.*;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Stack;
import java.io.IOException;

import zinara.ast.type.Type;
import zinara.ast.type.DictType;
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
	return ret.substring(0, ret.length()-2) + "}";
    }

    public void tox86(Genx86 generator)
	throws IOException, InvalidCodeException{
	Expression expr;

	String reg;
	String regAddr = generator.addrRegName(register);

	Iterator it = value.keySet().iterator();
	Stack st = new Stack();
	while(it.hasNext()) {
	    st.push(it.next());
	}
	while(! st.empty()) {
	    //Se genera el valor
	    expr = (Expression)value.get((String)st.pop());
	    expr.register = register;
	    reg = generator.regName(register, expr.type);

	    if (expr instanceof BooleanExp){
		String ret = generator.newLabel();
		boolValue(generator,expr,ret,reg);
		generator.writeLabel(ret);		    
	    }
	    else
		expr.tox86(generator);
	    
	    //Se pushea en la pila
	    if (!(expr instanceof ListExp)&&
		!(expr instanceof DictExp)&&
		!(expr instanceof TupleExp)&&
		!(expr instanceof StringExp))
		generator.write(generator.push(reg, expr.type.size()));
	}

	//Por ultimo, devuelvo la direccion donde comienza el diccionario
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