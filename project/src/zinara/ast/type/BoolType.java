package zinara.ast.type;

public class BoolType extends Type {
    public int size = 1;

    public BoolType() {}
    public String toString() { return "<BOOL>"; }
    public boolean equals(Type other) { return (other.getType() instanceof BoolType); }
    public Type getType() { return this; }
}
