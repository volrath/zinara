package zinara.ast.type;

import java.util.HashMap;
import java.util.Set;
import java.util.Iterator;

import zinara.exceptions.KeyErrorException;

public class DictType extends Type {
    private HashMap table;

    public DictType(HashMap t) {
	table = t;
    }

    public Iterator getIterator() { return table.keySet().iterator(); }

    public int size() { return table.size(); }

    public Type get(String key) { return (Type)table.get(key); }

    public Type getOrDie(String key) throws KeyErrorException {
	Type type = (Type)table.get(key);
	if (type == null)
	    throw new KeyErrorException("La clave " + key + " no se encuentra definida en el tipo de diccionario " + toString());
	return type;
    }

    public String toString() {
	String ret = "<{";
	Set keySet = table.keySet();
	Iterator it = keySet.iterator();
	String currentKey;
	while (it.hasNext()) {
	    currentKey = (String)it.next();
	    ret += currentKey + ": " + (Type)table.get(currentKey) + ", ";
	}
	return (ret + "}>");
    }

    public Type getType() { return this; }

    public boolean equals(Type other) {
	if (!(other instanceof DictType)) return false;
	DictType otherDict = (DictType)other;
	// Checks internally
	if (size() != otherDict.size()) return false;
	Iterator it1 = getIterator();
	Iterator it2 = otherDict.getIterator();
	String ckey1, ckey2;
	while(it1.hasNext()) {
	    ckey1 = (String)it1.next();
	    ckey2 = (String)it2.next();
	    if (ckey1 != ckey2 || !get(ckey1).equals(((Type)otherDict.get(ckey2)).getType()))
		return false;
	}
	return true;
    }
}

