package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.semantic.basicTypes;
//import zinara.symtable.SymTable;

public class IdentifierExp extends Expression {
    public String value;

    public IdentifierExp (String n) { value=n; }
    public Integer getType() { return new Integer(0); }
    public Integer getType(Type t) {
	if (t instanceof IntType)
	    return basicTypes.Int;
	else if (t instanceof FloatType)
	    return basicTypes.Float;
	else if (t instanceof CharType)
	    return basicTypes.Char;
	else if (t instanceof BoolType)
	    return basicTypes.Bool;
	else
	    return new Integer(0);
    }
}
