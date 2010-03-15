package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.ConstantType;
import zinara.symtable.*;

public class IdentifierExp extends Expression {
    public String value;
    private SymTable symtable;

    public IdentifierExp (String n, SymTable st) { value = n; symtable = st; }
    public Type getType() {
	Type type = symtable.getSymbol(value).getType();
	if (type instanceof ConstantType) type = ((ConstantType)type).getRealType();
	return type;
    }
    public String toString() { return value; }
}

