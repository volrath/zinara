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
}
