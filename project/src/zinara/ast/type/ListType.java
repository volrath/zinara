package zinara.ast.type;

public class ListType extends Type {
    private Type insideType;
    private int size;

    public ListType(Type it, int size) {
	insideType = it;
	this.size = size;
    }
    public ListType() { insideType = null; }

    public Type getInsideType() { return insideType; }
    public String toString() { return "<[" + insideType + "]>"; }
    public boolean equals(Type other) {
	if (!(other instanceof ListType)) return false;
	ListType otherList = (ListType)other;
	// For empty lists...
	if (otherList.getInsideType() == null) return true;
	// ...................
	return insideType.equals(otherList.getInsideType());
    }
    public Type getType() { return this; }

    public int size() { return this.size; }
}
