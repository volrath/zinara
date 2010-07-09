package zinara.ast.type;

public class StringType extends Type {
    public StringType() {}
    public String toString() { return (name.equals("") ? "<STRING>" : "<" + name + ">"); }
    public boolean equals(Type other) {
	if (other != null && (other.getType() instanceof StringType))
	    if (!other.getName().equals("") && !name.equals(""))
		return  other.getName().equals(name);
	    else
		return true;
	else
	    return false;
    }
    public Type getType() { return this; }
    public int size() { return name.length(); }
    public void setName(String n) { name = n; }
    public String getName() { return name; }
}
