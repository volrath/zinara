package zinara.ast.type;

public class IntType extends Type {
    public int size = 4;

    public IntType() {}
    public String toString() { return "<INT>"; }
    public Type getType() { return this; }
    public boolean equals(Type other) {
	if (other != null)
	    return (other.getType() instanceof IntType);
	else
	    return false;
    }
    public int size() { 
	return 4;
    }
}