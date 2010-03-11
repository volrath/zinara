package zinara.ast.expression;

import zinara.semantic.basicTypes;

public class FloatExp extends Expression {
   public float value;
   public FloatExp ( float n ) { value=n; }
    public Integer getType() { return basicTypes.Float; }
}
