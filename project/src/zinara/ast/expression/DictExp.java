package zinara.ast.expression;
import zinara.code_generator.*;

import java.util.HashMap;
import java.util.Iterator;

import zinara.ast.type.DictType;
import zinara.ast.type.Type;
import zinara.exceptions.InvalidDictionaryException;
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

    public void tox86(Genx86 generate){
    }
}