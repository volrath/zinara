package zinara.ast.type;

import zinara.ast.expression.Expression;
import zinara.exceptions.TypeClashException;

public class ListType extends Type {
    private Type insideType;
    private int len;

    public ListType(Type it, int s) throws TypeClashException {
	insideType = it;
	len = s;
    }
    public ListType() { insideType = null; }

    public Type getInsideType() { return insideType; }
    public int size() { return insideType.size() * len; }
    public String toString() { return "<[" + insideType + "|" + len + "]>"; }

    public boolean equals(Type other) {
	if (!(other instanceof ListType)) return false;
	ListType otherList = (ListType)other;
	// For empty lists...
	if (otherList.getInsideType() == null) return false;
	// ...................
	return insideType.equals(otherList.getInsideType()) && len == ((ListType)other).len();
    }

    public Type getType() { return this; }

    public int len() { return len; }
}
