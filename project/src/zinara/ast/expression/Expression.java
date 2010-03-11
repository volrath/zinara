package zinara.ast.expression;

import zinara.exceptions.TypeClashException;

public abstract class Expression {
    public abstract Integer getType() throws TypeClashException;
}
