package zinara.ast.type;

public class IntType extends Type {
    public int size = 4;

    public IntType() {}
    public String toString() { return (name.equals("") ? "<INT>" : "<" + name + ">"); }
    public Type getType() { return this; }
    public boolean equals(Type other) {
	if (other != null && (other.getType() instanceof IntType))
	    if (!other.getName().equals("") && !name.equals(""))
		return  other.getName().equals(name);
	    else
		return true;
	else
	    return false;
    }
    public int size() { 
	return 4;
    }

    public void setName(String n) { name = n; }
    public String getName() { return name; }
}