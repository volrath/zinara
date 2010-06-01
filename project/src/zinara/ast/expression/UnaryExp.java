package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.code_generator.Genx86;
import zinara.parser.parser;
import zinara.exceptions.TypeClashException;

public class UnaryExp extends Expression {
    public int operator;
    public Expression operand;
    
    public UnaryExp ( int o, Expression e ) throws TypeClashException { 
	operator=o;
	operand=e;
	type = parser.operators.check(this.operator, this.operand.getType(), null);
    }

    public Type getType() {
	return type;
   }

    public String toString() {
	return operator + " " + operand;
    }

    public void tox86(Genx86 generate){
    }

    public boolean isStaticallyKnown() { return operand.isStaticallyKnown(); }
}