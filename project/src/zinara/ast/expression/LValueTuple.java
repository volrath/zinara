package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.ast.type.TupleType;
import zinara.code_generator.Genx86;
import zinara.exceptions.KeyErrorException;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

public class LValueTuple extends LValue {
    private LValue constructor;
    private int index;

    // requires c.getType() be of Tuple type
    public LValueTuple(LValue c, int i)
	throws KeyErrorException, TypeClashException {
	// check if i is between the bounds of the type
	if (i < 0 || i >= ((TupleType)(c.getType().getType())).len())
	    throw new KeyErrorException("El indice " + i + " es mayor al tamano de la tupla (" + ((TupleType)c.getType()).len() + ")");

	constructor = c;
	index = i;
    }

    public Type getType() throws TypeClashException {
	if (type != null) return type;
	type = ((TupleType)(constructor.getType().getType())).get(index);
	return type;
    }
    public String toString() { return constructor + "[" + index + "]"; }

    public void tox86(Genx86 generator) throws IOException, InvalidCodeException {
	generator.write("; B-----\n");

	constructor.register = register;
	String constructorReg = generator.addrRegName(constructor.register);
	String valueReg       = generator.regName(constructor.register,type);

	//Deja la direccion en constructorReg
	currentDirection(generator);

	storeValue(generator, valueReg, constructorReg);

	generator.write("; E-----\n");
    }

    private void storeValue(Genx86 generator, String valueReg, String addrReg)
	throws IOException,InvalidCodeException {
	generator.write(generator.mov(valueReg,
				      "[" + addrReg + "]",
				      type.getType()
				      )
			);

	// if (type.getType() instanceof IntType)
	//     generator.write(generator.movInt(valueReg,
	// 				     "[" + addrReg + "]"));
	// else if (type.getType() instanceof FloatType)
	//     generator.write(generator.movReal(valueReg,
	// 				  "[" + addrReg + "]"));
	// else if (type.getType() instanceof BoolType)
	//     generator.write(generator.movBool(valueReg,
	// 				  "[" + addrReg + "]"));
	// else if ((type.getType() instanceof ListType)||
	// 	 (type.getType() instanceof DictType)){
	//     generator.write("; E-----\n");
	//     return;
	// }
	// else
	//     generator.write("Indexamiento de valores del tipo "+type.getType().toString()+" no implementado\n");
    }

    public void currentDirection(Genx86 generator) throws InvalidCodeException, IOException{
	String constructorReg = generator.addrRegName(constructor.register);
	constructor.currentDirection(generator);

	generator.write(generator.add(constructorReg,
				      Integer.toString(calculateOffsetForIndex())));
    }

    public int calculateOffsetForIndex() {
	int offset = 0;
	try {
	    Type t, constructorType = ((TupleType)(constructor.getType().getType()));
	    for (int i = 0; i < index; i++)
		offset += ((Type)((TupleType)constructorType).get(i)).size();
	} catch (TypeClashException e) { System.err.println("TypeClashException in LValueTuple.java:87 this should not happen"); }
	return offset;
    }


    public boolean isStaticallyKnown() {
	return false;
    }

    public Object staticValue() { return null; };

    public boolean isConstant() { return constructor.isConstant(); }
}