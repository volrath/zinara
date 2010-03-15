package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.FloatType;

public class FloatExp extends Expression {
    public float value;
    public FloatExp ( float n ) { value=n; }
    public Type getType() { return new FloatType(); }
    public String toString() { return Float.toString(value); }
}
