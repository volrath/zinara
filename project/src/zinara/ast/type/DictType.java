package zinara.ast.type;

import java.util.HashMap;
import java.util.Set;
import java.util.Iterator;

import zinara.exceptions.KeyErrorException;

public class DictType extends Type {
    private HashMap table; // HashMap of <String, Type>
    private HashMap offsets; // HashMap of <String, Int>   

    public DictType(HashMap t) {
	table = t;
	String key;
	Type ct;
	Iterator it = table.keySet().iterator();
	while(it.hasNext()) {
	    key = (String)it.next();
	    ct  = (Type)table.get(key);
	    offsets.put(key, new Integer(ct.size()));
	}
    }

    public Iterator getIterator() { return table.keySet().iterator(); }

    public int len() { return table.size(); }

    public int size() {
	int size = 0;
	Type ct;
	Iterator it = table.entrySet().iterator();
	while(it.hasNext()) {
	    ct = (Type)it.next();
	    size += ct.size();
	}
	return size;
    }

    public Type get(String key) { return (Type)table.get(key); }

    public Type getOrDie(String key) throws KeyErrorException {
	Type type = (Type)table.get(key);
	if (type == null)
	    throw new KeyErrorException("La clave " + key + " no se encuentra definida en el tipo de diccionario " + toString());
	return type;
    }

    public Integer getOffsetFor(String key) { return (Integer)offsets.get(key); }

    public String toString() {
	if (!name.equals("")) return "<" + name + ">";
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
	if (!otherDict.getName().equals("") && !name.equals("")) return  otherDict.getName().equals(name);
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

    public void setName(String n) { name = n; }
    public String getName() { return name; }
}

