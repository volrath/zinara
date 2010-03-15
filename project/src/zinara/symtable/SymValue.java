package zinara.symtable;

import zinara.ast.type.*;

public class SymValue{
    private boolean variable;
    private Type type;

    public SymValue(Type t, boolean var) {
	this.variable = var;
        this.type = t;
    }

    public Type getType() {
        return this.type;
    }

    public boolean isVariable() {
        return this.variable;
    }

    public String toString() {
	return "<" + (this.variable ? "Variable" : "Constant") + ": " + this.type + ">";
    }
}