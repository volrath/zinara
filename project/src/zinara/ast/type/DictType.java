package zinara.ast.type;

import java.util.HashMap;
import java.util.Set;
import java.util.Iterator;

public class DictType extends Type {
    private String name;
    private HashMap table;

    public DictType(HashMap t) {
	name = "";
	table = t;
    }

    public DictType(String n, HashMap t) {
	name = n;
	table = t;
    }

    public String getName() { return name; }

    public Iterator getIterator() { return table.keySet().iterator(); }

    public int size() { return table.size(); }

    public Type get(String key) { return (Type)table.get(key); }

    public String toString() {
	String ret = "<" + ((name == "") ? "{" : "<" + name + ">{");
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
	if (getName() != "" && otherDict.getName() != "")
	    if (getName() == otherDict.getName()) return true;
	    else return false;
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

