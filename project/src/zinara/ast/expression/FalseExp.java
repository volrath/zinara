package zinara.ast.expression;

import zinara.semantic.basicTypes;

public class FalseExp extends Expression {
   public FalseExp () {}
    public Integer getType() { return basicTypes.Bool; }
}
