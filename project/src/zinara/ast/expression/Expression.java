package zinara.ast.expression;

import zinara.utils.TypeClashException;

public abstract class Expression {
    public abstract Integer getType() throws TypeClashException;
}
