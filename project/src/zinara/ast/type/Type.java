package zinara.ast.type;

import java.util.Iterator;

public abstract class Type {
    protected String name = "";

    public abstract boolean equals(Type other);
    public abstract String toString();
    public abstract Type getType();
    public abstract int size();
    public abstract void setName(String n);
    public abstract String getName();
}
