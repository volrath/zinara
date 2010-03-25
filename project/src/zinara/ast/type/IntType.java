package zinara.ast.type;

public class IntType extends Type {
    public IntType() {}
    public String toString() { return "<INT>"; }
    public Type getType() { return this; }
    public boolean equals(Type other) { return (other.getType() instanceof IntType); }
}