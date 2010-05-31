package zinara.ast.type;

import zinara.ast.expression.Expression;

public class ConstantType extends Type {
    private Type type;
    private Expression value;

    public ConstantType(Type t, Expression v) {
	type = t; value = v;
    }
    public Type getRealType() { return type; }
    public Expression getValue() { return value; }
    public String toString() { return "Const" + type.toString(); }
    public Type getType() { return type; }
    public boolean equals(Type other) { return (type.equals(other.getType())); }
    public int size() { return type.size(); }
}