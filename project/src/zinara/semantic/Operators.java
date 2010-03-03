package zinara.semantic;

import zinara.parser.sym;
import zinara.utils.TypeClashException;

import java.util.Hashtable;

/*
  Does type cohersion and simple operator's type checking
 */
public class Operators {
    private class OP {
	int operator; 
	Integer rightType;
	Integer leftType;
	public OP(int o, Integer r, Integer l) { this.operator = o; this.rightType = r; this.leftType = l; }
    }

    public Hashtable table;
    public final int arithmetic = -1;
    public final int relational = -2;
    public final int logical    = -3;

    public Operators() {
	this.table = new Hashtable();
	/*
	  Binary Operators
	 */
	// Arithmetic
	this.table.put(this.new OP(this.arithmetic, basicTypes.Int, basicTypes.Int), basicTypes.Int);
	this.table.put(new OP(this.arithmetic, basicTypes.Float, basicTypes.Float), basicTypes.Float);
	this.table.put(new OP(this.arithmetic, basicTypes.Int, basicTypes.Float), basicTypes.Float);
	this.table.put(new OP(this.arithmetic, basicTypes.Float, basicTypes.Int), basicTypes.Float);
	//this.table.put(new OP(sym.PLUS, basicTypes.Char, basicTypes.Char), STRING);

	// Relational
	this.table.put(new OP(this.relational, basicTypes.Int, basicTypes.Int), basicTypes.Bool);
	this.table.put(new OP(this.relational, basicTypes.Float, basicTypes.Float), basicTypes.Bool);
	this.table.put(new OP(this.relational, basicTypes.Char, basicTypes.Char), basicTypes.Bool);
	this.table.put(new OP(this.relational, basicTypes.Bool, basicTypes.Bool), basicTypes.Bool);
	this.table.put(new OP(this.relational, basicTypes.Int, basicTypes.Float), basicTypes.Bool);
	this.table.put(new OP(this.relational, basicTypes.Float, basicTypes.Int), basicTypes.Bool);

	// Logical
	this.table.put(new OP(this.logical, basicTypes.Int, basicTypes.Int), basicTypes.Bool);
	this.table.put(new OP(this.logical, basicTypes.Float, basicTypes.Float), basicTypes.Bool);
	this.table.put(new OP(this.logical, basicTypes.Bool, basicTypes.Bool), basicTypes.Bool);
	this.table.put(new OP(this.logical, basicTypes.Int, basicTypes.Float), basicTypes.Bool);
	this.table.put(new OP(this.logical, basicTypes.Float, basicTypes.Int), basicTypes.Bool);

	/*
	  Unary Operators
	 */
	this.table.put(new OP(sym.NOEQ, basicTypes.Int, null), basicTypes.Bool);
	this.table.put(new OP(sym.NOEQ, basicTypes.Float, null), basicTypes.Bool);
	this.table.put(new OP(sym.NOEQ, basicTypes.Bool, null), basicTypes.Bool);

	this.table.put(new OP(sym.UMINUS, basicTypes.Int, null), basicTypes.Int);
	this.table.put(new OP(sym.UMINUS, basicTypes.Float, null), basicTypes.Float);
    }

    // also returns the type cohersion if needed
    public Integer check(int o, Integer r, Integer l) throws TypeClashException {
	try {
	    return (Integer)this.table.get(new OP(o,r,l));
	} catch (NullPointerException e) {
	    throw new TypeClashException("Error de tipos con el operador " + o + " en la linea tal..."); // mejorar
	}
    }
}
