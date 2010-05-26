package zinara.ast.type;

import java.util.Iterator;

public abstract class Type {
    public int size;

    public abstract boolean equals(Type other);
    public String toString() { return super.toString(); };
    public abstract Type getType();
}
