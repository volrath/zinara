package zinara.ast.type;

public class BoolType extends Type {
    public int size = 4;

    public BoolType() {}
    public String toString() { return (name.equals("") ? "<BOOL>" : "<" + name + ">"); }
    public boolean equals(Type other) {
	if (other != null && (other.getType() instanceof BoolType))
	    if (!other.getName().equals("") && !name.equals(""))
		return  other.getName().equals(name);
	    else
		return true;
	else
	    return false;
    }
    public Type getType() { return this; }
    public int size() { return this.size; }
    public void setName(String n) { name = n; }
    public String getName() { return name; }
}
