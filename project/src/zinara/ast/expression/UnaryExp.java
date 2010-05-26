package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.parser.parser;
import zinara.exceptions.TypeClashException;

public class UnaryExp extends Expression {
    public int operator;
    public Expression operand;
    
    public UnaryExp ( int o, Expression e ) { operator=o; operand=e; }

    public Type getType() throws TypeClashException {
	if (type != null) return type;
	type = parser.operators.check(this.operator, this.operand.getType(), null);
	return type;
   }

    public String toString() {
	return operator + " " + operand;
    }

    public void tox86(Genx86 generate){
    }
}