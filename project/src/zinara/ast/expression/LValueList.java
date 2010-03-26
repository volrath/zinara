package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.ListType;
import zinara.exceptions.TypeClashException;

public class LValueList extends LValue {
    private LValue constructor;
    private Expression index;

    // requires c.getType() be of List[something] type
    // requires e be of IntType type
    public LValueList(LValue c, Expression e) {
	constructor = c;
	index = e;
    }

    public Type getType() throws TypeClashException {
	return ((ListType)constructor.getType()).getInsideType();
    }
    public String toString() { return constructor + "[" + index + "]"; }
}