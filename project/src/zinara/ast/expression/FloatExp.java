package zinara.ast.expression;

import zinara.ast.type.basicTypes;

public class FloatExp extends Expression {
   public float value;
   public FloatExp ( float n ) { value=n; }
    public int getType() { return basicTypes.Float; }
}
