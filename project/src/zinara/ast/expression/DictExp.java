package zinara.ast.expression;

import java.util.HashMap;
import java.util.Iterator;

import zinara.ast.type.DictType;
import zinara.ast.type.Type;

// invariant: value is at least 2 long
public class DictExp extends Expression {
    public HashMap value; // arraylist of expressions

    public DictExp(HashMap v) { value = v; }
    public DictExp() { value = new HashMap(); }

    public Type getType() { 
// 	if (value.size() > 0)
// 	    return new ListType(((Expression)value.get(0)).getType());
// 	else return new ListType(null);
	return new DictType(null); // typeclashexception handling... heavy
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