package zinara.ast.expression;

import zinara.ast.type.BoolType;
import zinara.ast.type.FloatType;
import zinara.ast.type.IntType;
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
	String constructorReg = generator.regName(constructor.register);
	String indexReg       = generator.regName(index.register);

	constructor.tox86(generator);
	// Save, i dont know how to do this
	index.tox86(generator);

	// Save again, it seems, dont really know.
	generator.write(generator.imul(indexReg,
				       Integer.toString(type.size())));

	// Restore something
	generator.write(generator.add(constructorReg,
				      indexReg));
	// And restore again

	if ((type.getType() instanceof IntType)||
	    (type.getType() instanceof FloatType)||
	    (type.getType() instanceof BoolType))
	    generator.write(generator.mov(constructorReg,
					  "[" + constructorReg + "]"));
	else if (type.getType() instanceof ListType){
	    generator.write("; E-----\n");
	    return;
	}
	else
	    generator.write("Indexamiento de valores del tipo "+type.getType().toString()+" no implementado\n");	    

	// if (isExpression()) {
	//     if (isBool())
	// 	writeBooleanExpression(generator);
	//     else
	// 	writeExpression(generator);
	// }
	generator.write("; E-----\n");
    }
}