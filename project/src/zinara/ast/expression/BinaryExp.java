package zinara.ast.expression;

import zinara.parser.parser;
import zinara.utils.TypeClashException;

public class BinaryExp extends Expression {
    public int operator;
    public Expression left;
    public Expression right;
    
    public BinaryExp (int o, Expression l, Expression r) { operator=o; left=l; right=r; }
    
    public Integer getType() throws TypeClashException {
	return parser.operators.check(this.operator, this.left.getType(), this.right.getType());
    }
}
