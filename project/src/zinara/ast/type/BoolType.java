package zinara.ast.type;

public class BoolType extends Type {
    public int size = 1;

    public BoolType() {}
    public String toString() { return "<BOOL>"; }
    public boolean equals(Type other) { return (other.getType() instanceof BoolType) && other.getName().equals(name); }
    public Type getType() { return this; }
    public int size() { return this.size; }
    public void setName(String n) { name = n; }
    public String getName() { return name; }
}
