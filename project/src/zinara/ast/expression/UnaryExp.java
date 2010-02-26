package zinara.ast.expression;

import zinara.ast.type.basicTypes;
import zinara.parser.sym;

public class UnaryExp extends Expression {
    public int operator;
    public Expression operand;
    
    public UnaryExp ( int o, Expression e ) { operator=o; operand=e; }

    public int getType() {
	if (this.operator == sym.UMINUS) {
	    if (this.operand.getType() == basicTypes.Int)
		return basicTypes.Int;
	    else if (this.operand.getType() == basicTypes.Float)
		return basicTypes.Float;
	    else {
		System.out.println("Error de tipos sobre el operador " + this.operator + " y la expresion " + this.operand); // Change this for a custom exception
		return 0;
	    }
	}
	else if (this.operator == sym.NOEQ) {
	    if (this.operand.getType() == basicTypes.Char) {
		System.out.println("Error de tipos sobre el operador " + this.operator + " y la expresion " + this.operand); // Change this for a custom exception
		return 0;
	    } else return basicTypes.Bool;
	}
	else
	    return 0;
    }
}