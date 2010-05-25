package zinara.ast.type;

import java.util.ArrayList;

public class TupleType extends Type {
    private ArrayList types; // arraylist of types

    public TupleType(ArrayList ts) {
	types = ts;
	size = 0;
	for (int i = 0; i < types.size(); i++)
	    size += ((Type)types.get(i)).size;
    }
    public TupleType() { types = null; }

    public int len() { return types.size(); }

    public Type get(int i) { return (Type)types.get(i); }

    public String toString() {
	return super.toString();
// 	String ret = "<(";
// 	for (int i = 0; i < types.len(); i++)
// 	    ret += (Type)types.get(i) + ", ";
// 	return ret.substring(0, ret.length()-2) + ")>";
    }

    public Type getType() { return this; }

    public boolean equals(Type other) {
	if (!(other instanceof TupleType)) return false;
	TupleType otherTuple = (TupleType)other;
	if (otherTuple.len() == 0) return true;
	if (len() != otherTuple.len()) return false;
	for (int i = 0; i < len(); i++)
	    if (!get(i).equals(otherTuple.get(i))) return false;
	return true;
    }
}
