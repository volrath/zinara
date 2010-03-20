package zinara.ast.type;

public class BoolType extends Type {
    public BoolType() {}
    public String toString() { return "<BOOL>"; }
    public boolean equals(Type other) { return (other.getType() instanceof BoolType); }
    public Type getType() { return this; }
}
