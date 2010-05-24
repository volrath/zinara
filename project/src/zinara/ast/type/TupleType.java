package zinara.ast.type;

import java.util.ArrayList;

public class TupleType extends Type {
    private ArrayList types; // arraylist of types

    public TupleType(ArrayList ts) { types = ts; }
    public TupleType() { types = null; }

    public int size() { return types.size(); }

    public Type get(int i) { return (Type)types.get(i); }

    public String toString() {
	return super.toString();
// 	String ret = "<(";
// 	for (int i = 0; i < types.size(); i++)
// 	    ret += (Type)types.get(i) + ", ";
// 	return ret.substring(0, ret.length()-2) + ")>";
    }

    public Type getType() { return this; }

    public boolean equals(Type other) {
	if (!(other instanceof TupleType)) return false;
	TupleType otherTuple = (TupleType)other;
	if (otherTuple.size() == 0) return true;
	if (size() != otherTuple.size()) return false;
	for (int i = 0; i < size(); i++)
	    if (!get(i).equals(otherTuple.get(i))) return false;
	return true;
    }
}
