package zinara.symtable;

import zinara.ast.type.*;
import zinara.code_generator.Genx86;

public class SymValue{
    private Status status;
    public Type type; //@ invariant type != null;

    //Variables pertinentes a la generacion de codigo
    private int offset = 0;

    //@ requires t != null;
    public SymValue(Type t, Status s) {
	this.status = s;
        this.type = t;
    }

    //@ ensures \result != null;
    public Type getType() { 
	return type;
    }

    public boolean isVariable() { return status instanceof Variable; }

    public Status getStatus() { return status; }

    public int getOffset() { return offset; }
    public void setOffset(int os) { offset = os; }

    public String toString() {
    	return "<" + (isVariable() ? "Variable" : "Constant") + ": " + this.type + ">";
    }
}