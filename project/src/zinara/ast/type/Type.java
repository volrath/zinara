package zinara.ast.type;

import java.util.Iterator;

public abstract class Type {
    public abstract boolean equals(Type other);
    public abstract String toString();
    public abstract Type getType();
}
