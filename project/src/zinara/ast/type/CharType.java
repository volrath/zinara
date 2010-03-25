package zinara.ast.type;

public class CharType extends Type {
    public CharType() {}
    public String toString() { return "<CHAR>"; }
    public boolean equals(Type other) { return (other.getType() instanceof CharType); }
    public Type getType() { return this; }
}
