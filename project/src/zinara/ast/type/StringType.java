package zinara.ast.type;

public class StringType extends Type {
    public StringType() {}
    public String toString() { return "<STRING>"; }
    public boolean equals(Type other) { return (other.getType() instanceof StringType); }
    public Type getType() { return this; }
}
