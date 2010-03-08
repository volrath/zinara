package zinara.ast;

import zinara.ast.type.*;
import zinara.ast.instructions.*;

public class SymDef extends SymValue{
    private CodeBlock code;
    private Symtable symt;
    private Type type;

    public SymDef(CodeBlock cb, Symtable sym, Type t) {
	this.code = cb;
        this.symt = sym;
        this.type = t;
    }

    public CodeBlock getCode(){
        return this.code;
    }

    public Type getType() {
        return this.type;
    }

    public Symtable getSymtable() {
        return this.symt;
    }
}