package zinara.ast.expression;

import java.util.HashMap;
import java.util.Iterator;

import zinara.ast.type.DictType;
import zinara.ast.type.Type;

public class DictExp extends Expression {
    public HashMap value; // hashmap of string:expr

    public DictExp(HashMap v) { value = v; }
    public DictExp() { value = new HashMap(); }

    public Type getType() {
	HashMap typemap = new HashMap();
	Iterator it = value.keySet().iterator();
	String ckey;
	while(it.hasNext()) {
	    ckey = (String)it.next();
	    if (typemap.put(ckey, ((Expression)value.get(ckey)).getType()))
		throw new InvalidDictionaryException("La clave " + ckey + " se repite en el diccionario " + this);
	}
	return new DictType(typemap);
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
}