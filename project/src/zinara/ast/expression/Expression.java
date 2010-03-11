package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.exceptions.TypeClashException;

public abstract class Expression {
    public abstract Type getType() throws TypeClashException;
}
