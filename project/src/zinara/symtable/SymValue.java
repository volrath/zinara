package zinara.symtable;

import zinara.ast.type.*;

public class SymValue{
    private boolean variable;
    public Type type; //@ invariant type != null;

    //Variables pertinentes a la generacion de codigo
    private int offset = 0;

    //@ requires t != null;
    public SymValue(Type t, boolean var) {
	this.variable = var;
        this.type = t;
    }

    //@ ensures \result != null;
    public Type getType() { return this.type; }

    public boolean isVariable() { return this.variable; }

    public int getOffset() { return offset; }
    public void setOffset(int os) { offset = os; }

    public String toString() {
    	return "<" + (this.variable ? "Variable" : "Constant") + ": " + this.type + ">";
    }
}