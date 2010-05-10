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
	return parser.operators.check(this.operator, this.operand.getType(), null);
   }

    public String toString() {
	return operator + " " + operand;
    }

    public String tox86(Genx86 generate){
        return "";
    }
}