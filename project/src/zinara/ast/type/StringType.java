package zinara.ast.type;

public class StringType extends Type {
    public StringType() {}
    public String toString() { return "[STRING]"; }
    public Type getType() { return this; }
}
