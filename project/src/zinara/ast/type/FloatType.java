package zinara.ast.type;

public class FloatType extends Type {
    public int size = 4;

    public FloatType() {}
    public String toString() { return "<FLOAT>"; }
    public Type getType() { return this; }
    public boolean equals(Type other) { return (other.getType() instanceof FloatType); }
}
