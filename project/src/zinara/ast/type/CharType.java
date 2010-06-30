package zinara.ast.type;

public class CharType extends Type {
    public int size = 1;

    public CharType() {}
    public String toString() { return "<CHAR>"; }
    public boolean equals(Type other) { return (other.getType() instanceof CharType); }
    public Type getType() { return this; }
    public int size() { return this.size; }
    public void setName(String n) { name = n; }
    public String getName() { return name; }
}
