package zinara.ast.expression;

import zinara.ast.type.basicTypes;
import zinara.parser.sym;

public class BinaryExp extends Expression {
    public int operator;
    public Expression left;
    public Expression right;
    
    public BinaryExp (int o, Expression l, Expression r) { operator=o; left=l; right=r; }
    
    public int getType() {
	// Arithmetic operators
	if (this.operator == sym.PLUS || this.operator == sym.MINUS || this.operator == sym.TIMES || this.operator == sym.DIVIDE ||
	    this.operator == sym.MOD || this.operator == sym.POW) {
	    if (this.left.getType() == this.right.getType()) {
		if (this.left.getType() == basicTypes.Int || this.left.getType() == basicTypes.Float)
		    return this.left.getType();
		else {
		    System.out.println("Error de tipos en el operador " + this.operator + " y las expresiones " + this.left + " y " + this.right);
		    return 0;
		}
	    } else {
		if ((this.left.getType() == basicTypes.Int && this.right.getType() == basicTypes.Float) ||
		    (this.left.getType() == basicTypes.Float && this.right.getType() == basicTypes.Int))
		    return basicTypes.Float;
		else {
		    System.out.println("Error de tipos en el operador " + this.operator + " y las expresiones " + this.left + " y " + this.right);
		    return 0;
		}
	    }
	}

	// Relational operators
	if (this.operator == sym.GT || this.operator == sym.LT || this.operator == sym.GTE || this.operator == sym.LTE || this.operator == sym.SHEQ ||
	    this.operator == sym.DEEQ) {
	    if (this.left.getType() == this.right.getType())
		return basicTypes.Bool;
	    else {
		System.out.println("Error de tipos en el operador " + this.operator + " y las expresiones " + this.left + " y " + this.right);
		return 0;
		/// F I X  this...
	    }
	}

	return 0;
    }
}
