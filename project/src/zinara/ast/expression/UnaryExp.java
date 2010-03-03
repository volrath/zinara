package zinara.ast.expression;

import zinara.parser.parser;
import zinara.utils.TypeClashException;

public class UnaryExp extends Expression {
    public int operator;
    public Expression operand;
    
    public UnaryExp ( int o, Expression e ) { operator=o; operand=e; }

    public Integer getType() throws TypeClashException {
	return parser.operators.check(this.operator, this.operand.getType(), null);
   }
}