package zinara.ast.expression;

import zinara.ast.type.basicTypes;

public class TrueExp extends Expression {
    public TrueExp () {}
    public int getType() { return basicTypes.Bool; }
}
