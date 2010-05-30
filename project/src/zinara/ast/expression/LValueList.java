package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.ListType;
import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

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
	if (type != null) return type;
	type = ((ListType)constructor.getType().getType()).getInsideType();
	return type;
    }
    public String toString() { return constructor + "[" + index + "]"; }

    public void tox86(Genx86 generator) throws IOException {
	generator.write("; B-----\n");

	constructor.register = register;
	index.register       = register + 1;

	constructor.tox86(generator);
	// Save, i dont know how to do this
	index.tox86(generator);

	// Save again, it seems, dont really know.
	generator.write(generator.imul(generator.regName(index.register), Integer.toString(type.size())));

	// Restore something
	generator.write(generator.add(generator.regName(constructor.register), generator.regName(index.register)));
	// And restore again

	if (isExpression()) {
	    if (isBool())
		writeBooleanExpression(generator);
	    else
		writeExpression(generator);
	}
	generator.write("; E-----\n");
    }
}