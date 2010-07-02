package zinara.ast.type;

public class CharType extends Type {
    public int size = 1;

    public CharType() {}
    public String toString() { return (name.equals("") ? "<CHAR>" : "<" + name + ">"); }
    public boolean equals(Type other) {
	if (other != null && (other.getType() instanceof CharType))
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
