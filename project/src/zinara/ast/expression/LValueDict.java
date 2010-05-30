package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.DictType;
import zinara.exceptions.KeyErrorException;
import zinara.exceptions.TypeClashException;
import zinara.code_generator.Genx86;

import java.io.IOException;

public class LValueDict extends LValue {
    private LValue constructor;
    private String identifier;

    // requires c.getType() be of DictType
    public LValueDict(LValue c, String i)
	throws KeyErrorException, TypeClashException {
	// check if i is in the dictionary
	((DictType)c.getType().getType()).getOrDie(i);

	constructor = c;
	identifier = i;
    }

    public Type getType() throws TypeClashException {
	if (type != null) return type;
	type = ((DictType)constructor.getType().getType()).get(identifier);
	return type;
    }
    public String toString() { return constructor + "[" + identifier + "]"; }

    public void tox86(Genx86 generator) throws IOException {
	constructor.register = register;
	constructor.tox86(generator);

	// Get the identifier offset
	try {
	    Integer offset = ((DictType)constructor.getType().getType()).getOffsetFor(identifier);
	    generator.write(generator.add(generator.regName(register), offset.toString()));
	} catch (TypeClashException e) {}

	if (isExpression()) {
	    if (isBool())
		writeBooleanExpression(generator);
	    else
		writeExpression(generator);
	}

    }
}