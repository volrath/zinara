package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.exceptions.TypeClashException;

public abstract class Expression {
    //@ ensures \result != null
    public abstract Type getType() throws TypeClashException;
    public abstract String toString();
}
