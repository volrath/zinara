package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.ast.type.BoolType;
import zinara.ast.type.FloatType;
import zinara.ast.type.IntType;
import zinara.ast.type.ListType;
import zinara.ast.type.DictType;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;
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

    public void tox86(Genx86 generator) throws IOException,InvalidCodeException {
	generator.write("; B-----\n");

	constructor.register = register;
	index.register       = register + 1;
	try {
	    String constructorReg = generator.addrRegName(constructor.register);
	    String valueReg       = generator.regName(constructor.register, getType());
	    String indexReg       = generator.intRegName(index.register);

	    //Deja la direccion en constructorReg
	    currentDirection(generator);

	    storeValue(generator, valueReg, constructorReg);
	} catch(TypeClashException e) {}

	generator.write("; E-----\n");
    }

    private void storeValue(Genx86 generator, String valueReg, String addrReg)  throws IOException{
	if (type.getType() instanceof IntType)
	    generator.write(generator.movInt(valueReg,
					     "[" + addrReg + "]"));
	else if (type.getType() instanceof FloatType)
	    generator.write(generator.movReal(valueReg,
					  "[" + addrReg + "]"));
	else if (type.getType() instanceof BoolType)
	    generator.write(generator.movBool(valueReg,
					  "[" + addrReg + "]"));
	else if ((type.getType() instanceof ListType)||
		 (type.getType() instanceof DictType)){
	    generator.write("; E-----\n");
	    return;
	}
	else
	    generator.write("Indexamiento de valores del tipo "+type.getType().toString()+" no implementado\n");
    }

    public void currentDirection(Genx86 generator)throws InvalidCodeException, IOException{
	constructor.register = register;
	index.register       = register + 1;
	String constructorReg = generator.addrRegName(constructor.register);
	String indexReg       = generator.intRegName(index.register);

	//Ver NOTA
	String offsetReg      = generator.addrRegName(index.register);

	constructor.currentDirection(generator);

	// Save, i dont know how to do this
	index.tox86(generator);

	// Save again, it seems, dont really know.
	generator.write(generator.imul(indexReg,
				       Integer.toString(new IntType().size())));

	// Restore something
	generator.write(generator.add(constructorReg,
				      offsetReg));
	// And restore again	
    }
    /*****NOTA*****/
    /* Los enteros, para 64bits, son de 32bits, pero las direcciones
    son de 64bits, no puedes sumar registros de 32 y 64, asi que
    necesito el nombre del registro de 64bits donde esta guardado
    en indice*/

    public boolean isStaticallyKnown() {
	// for now,
	return false;
    }

    public Object staticValue() { return null; };

    public boolean isConstant() { return constructor.isConstant(); }
}