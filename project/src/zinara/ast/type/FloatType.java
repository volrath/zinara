package zinara.ast.type;

public class FloatType extends Type {
    public int size = 8;

    public FloatType() {}
    public String toString() { return (name.equals("") ? "<FLOAT>" : "<" + name + ">"); }
    public Type getType() { return this; }
    public boolean equals(Type other) {
	if (other != null && (other.getType() instanceof FloatType))
	    if (!other.getName().equals("") && !name.equals(""))
		return  other.getName().equals(name);
	    else
		return true;
	else
	    return false;
    }
    public int size() { return this.size; }
    public void setName(String n) { name = n; }
    public String getName() { return name; }
}
