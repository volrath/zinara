package zinara.ast.type;

public class ListType extends Type {
    private Type insideType;
    private int size;

    public ListType(Type it, int s) {
	insideType = it;
	size = s;
    }
    public ListType() { insideType = null; }

    public Type getInsideType() { return insideType; }
    public int getSize() { return size; }
    public String toString() { return "<[" + insideType + "|" + size + "]>"; }

    public boolean equals(Type other) {
	if (!(other instanceof ListType)) return false;
	ListType otherList = (ListType)other;
	// For empty lists...
	if (otherList.getInsideType() == null) return true;
	// ...................
	return insideType.equals(otherList.getInsideType()) && size == ((ListType)other).getSize();
    }

    public Type getType() { return this; }

    public int size() { return this.size; }
}
