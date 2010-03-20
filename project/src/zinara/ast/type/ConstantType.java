package zinara.ast.type;

public class ConstantType extends Type {
    private Type type;
    private Object value;

    public ConstantType(Type t, Object v) {
	type = t; value = v;
    }
    public Type getRealType() { return type; }
    public String toString() { return type.toString(); }
    public Type getType() { return type; }
    public boolean equals(Type other) { return (type.equals(other.getType())); }
}