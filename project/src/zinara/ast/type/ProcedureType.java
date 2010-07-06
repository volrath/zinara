package zinara.ast.type;

import java.util.ArrayList;

import zinara.ast.instructions.CodeBlock;

public class ProcedureType extends RoutineType {
    public ProcedureType(ArrayList al, CodeBlock cb) { 
	this.args = al;
	this.codeBlock = cb;
    }

    public int size() { return 0; }

    public Type getType() { return this; }

    public boolean equals(Type other) {
	return false;
    }
}
