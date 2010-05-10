package zinara.symtable;

import zinara.ast.type.*;

public class SymValue{
    private boolean variable;
    private Type type; //@ invariant type != null;

    //Variables pertinentes a la generacion de codigo
    private int desp;
    private int size;

    //@ requires t != null;
    public SymValue(Type t, boolean var) {
	this.variable = var;
        this.type = t;
	this.desp = 0;
	this.size = 4; //Hay que arreglar esto
    }

    //@ ensures \result != null;
    public Type getType() { return this.type; }

    public int getSize() { return this.size; }

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