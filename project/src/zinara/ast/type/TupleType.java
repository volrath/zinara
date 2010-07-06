package zinara.ast.type;

import java.util.ArrayList;

public class TupleType extends Type {
    private ArrayList types; // arraylist of types

    public TupleType(ArrayList ts) { types = ts; }
    public TupleType() { types = null; }

    public int len() { return types.size(); }

    public int size() {
	int size = 0;
	for (int i = 0; i < types.size(); i++)
	    size += ((Type)types.get(i)).size();
	return size;
    }

    public Type get(int i) { return (Type)types.get(i); }

    public String toString() {
	if (!name.equals("")) return "<" + name + ">";
	String ret = "<(";
	for (int i = 0; i < types.size(); i++)
	    ret += (Type)types.get(i) + ", ";
	return ret.substring(0, ret.length()-2) + ")>";
    }

    public Type getType() { return this; }

    public boolean equals(Type other) {
	if (other != null && !(other instanceof TupleType)) return false;
	TupleType otherTuple = (TupleType)other;
	//if (otherTuple.len() == 0) return true;
	if (!otherTuple.getName().equals("") && !name.equals("")) return  otherTuple.getName().equals(name);
	if (len() != otherTuple.len()) return false;
	for (int i = 0; i < len(); i++)
	    if (!get(i).equals(otherTuple.get(i))) return false;
	return true;
    }

    public void setName(String n) { name = n; }
    public String getName() { return name; }
}
