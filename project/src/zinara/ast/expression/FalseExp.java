package zinara.ast.expression;

import zinara.ast.type.basicTypes;

public class FalseExp extends Expression {
   public FalseExp () {}
    public int getType() { return basicTypes.Bool; }
}
