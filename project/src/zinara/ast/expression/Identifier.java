package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.code_generator.Genx86;
import zinara.symtable.*;

import java.io.IOException;

public class Identifier extends LValue {
    private String identifier;
    private SymTable symtable;

    public Identifier (String id, SymTable st) {
	identifier = id;
	symtable = st;
    }

    public String getIdentifier() { return identifier; }
    public SymTable getSymTable() { return symtable; }
    public SymValue getSymValue(){
	return symtable.getSymbol(identifier);
    }

    public Type getType() {
	if (type != null) return type;
	type = symtable.getSymValueForId(identifier).getType();
	return type;
    }
    public String toString() { return identifier; }

    public void tox86(Genx86 generator) throws IOException {
	generator.write(generator.mov(generator.current_reg(), ""+getSymValue().getOffset()));
	generator.write(generator.add(generator.current_reg(), generator.global_space()));
    }

    public String currentDirection(Genx86 generator) {
	return generator.global_space() + "+" + getSymValue().getOffset();
    }
}
