package zinara.ast.expression;

import zinara.semantic.basicTypes;

public class TrueExp extends Expression {
    public TrueExp () {}
    public Integer getType() { return basicTypes.Bool; }
}
