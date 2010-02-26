package zinara.ast.expression;

import zinara.ast.Symtable;
import zinara.ast.type.*;

public class IdentifierExp extends Expression {
    public String value;

    public IdentifierExp (String n) { value=n; }
    public int getType() { return 0; }
    public int getType(Type t) {
	if (t instanceof IntType)
	    return basicTypes.Int;
	else if (t instanceof FloatType)
	    return basicTypes.Float;
	else if (t instanceof CharType)
	    return basicTypes.Char;
	else if (t instanceof BoolType)
	    return basicTypes.Bool;
	else
	    return 0;
    }
}
