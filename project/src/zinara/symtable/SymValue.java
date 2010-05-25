package zinara.symtable;

import zinara.ast.type.*;

public class SymValue{
    private boolean variable;
    public Type type; //@ invariant type != null;

    //Variables pertinentes a la generacion de codigo
    private int desp;

    //@ requires t != null;
    public SymValue(Type t, boolean var) {
	this.variable = var;
        this.type = t;
	this.desp = 0;
    }

    //@ ensures \result != null;
    public Type getType() { return this.type; }

    public boolean isVariable() { return this.variable; }

    public int getDesp(){
	return this.desp;
    }

    public void setDesp(int d){
	this.desp = d;
    }

    public String toString() {
    	return "<" + (this.variable ? "Variable" : "Constant") + ": " + this.type + ">";
    }
}