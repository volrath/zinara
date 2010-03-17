package zinara.ast.type;

public class ListType extends Type {
    private Type insideType;

    public ListType(Type it) {
	insideType = it;
    }

    public Type getInsideType() { return insideType; }
    public String toString() { return "<[" + insideType + "]>"; }
    public Type getType() { return this; }
}
