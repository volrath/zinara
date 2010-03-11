package zinara.semantic;

import java.util.Hashtable;

import zinara.ast.type.*;
import zinara.exceptions.TypeClashException;
import zinara.parser.sym;

/*
  Does type cohersion and simple operator's type checking
 */
public class Operators {
    private class OP {
	int operator; 
	Type rightType;
	Type leftType;
	public OP(int o, Type r, Type l) { this.operator = o; this.rightType = r; this.leftType = l; }

	public boolean equals(OP other) {
	    return (this.leftType == other.leftType) && (this.rightType == other.rightType);
	}
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
	this.table.put(this.new OP(this.arithmetic, new IntType(), new IntType()), new IntType()); // new IntType() -> new IntType()
	this.table.put(new OP(this.arithmetic, new FloatType(), new FloatType()), new FloatType());
	this.table.put(new OP(this.arithmetic, new IntType(), new FloatType()), new FloatType());
	this.table.put(new OP(this.arithmetic, new FloatType(), new IntType()), new FloatType());
	//this.table.put(new OP(sym.PLUS, new CharType(), new CharType()), STRING);

	// Relational
	this.table.put(new OP(this.relational, new IntType(), new IntType()), new BoolType());
	this.table.put(new OP(this.relational, new FloatType(), new FloatType()), new BoolType());
	this.table.put(new OP(this.relational, new CharType(), new CharType()), new BoolType());
	this.table.put(new OP(this.relational, new BoolType(), new BoolType()), new BoolType());
	this.table.put(new OP(this.relational, new IntType(), new FloatType()), new BoolType());
	this.table.put(new OP(this.relational, new FloatType(), new IntType()), new BoolType());

	// Logical
	this.table.put(new OP(this.logical, new IntType(), new IntType()), new BoolType());
	this.table.put(new OP(this.logical, new FloatType(), new FloatType()), new BoolType());
	this.table.put(new OP(this.logical, new BoolType(), new BoolType()), new BoolType());
	this.table.put(new OP(this.logical, new IntType(), new FloatType()), new BoolType());
	this.table.put(new OP(this.logical, new FloatType(), new IntType()), new BoolType());

	/*
	  Unary Operators
	 */
	this.table.put(new OP(sym.NOEQ, new IntType(), null), new BoolType());
	this.table.put(new OP(sym.NOEQ, new FloatType(), null), new BoolType());
	this.table.put(new OP(sym.NOEQ, new BoolType(), null), new BoolType());

	this.table.put(new OP(sym.UMINUS, new IntType(), null), new IntType());
	this.table.put(new OP(sym.UMINUS, new FloatType(), null), new FloatType());
    }

    // also returns the type cohersion if needed
    public Type check(int o, Type r, Type l) throws TypeClashException {
	try {
	    return (Type)this.table.get(new OP(o,r,l));
	} catch (NullPointerException e) {
	    throw new TypeClashException("Error de tipos con el operador " + o + " en la linea tal..."); // mejorar
	}
    }
}
