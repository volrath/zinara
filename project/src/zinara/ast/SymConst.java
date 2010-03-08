package zinara.ast;

import zinara.ast.type.*;

public class SymConst extends SymValue{
    private boolean variable;
    private Object value;
    private Type type;

    public SymConst(Object v, Type t, boolean var) {
	this.variable = var;
        this.value = v;
        this.type = t;
    }

    public Object getValue(){
        return this.value;
    }

    public Type getType() {
        return this.type;
    }

    public boolean isCons() {
        return ! this.variable;
    }
}