package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.symtable.SymTable;

public class Identifier extends LValue {
    private String identifier;
    private SymTable symtable;

    public Identifier(String id, SymTable st) {
	identifier = id;
	symtable = st;
    }

    public String getIdentifier() { return identifier; }
    public SymTable getSymTable() { return symtable; }

    public Type getType() {
	return symtable.getSymValueForId(identifier).getType();
    }
    public String toString() { return identifier; }
}
