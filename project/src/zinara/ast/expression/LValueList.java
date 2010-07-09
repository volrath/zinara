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

    public void tox86(Genx86 generator)
	throws IOException,InvalidCodeException{
	generator.write("; B-----\n");

	try {
	    constructor.register = register;
	    String constructorReg = generator.addrRegName(constructor.register);
	    String valueReg       = generator.regName(constructor.register,getType());

	    //Esto deja la direccion en constructorReg
	    currentDirection(generator);

	    storeValue(generator, valueReg, constructorReg);
	} catch(TypeClashException e) {}

	generator.write("; E-----\n");
    }

    private void storeValue(Genx86 generator, String valueReg, String addrReg)
	throws IOException,InvalidCodeException{
	generator.write(generator.mov(valueReg,
				      "[" + addrReg + "]",
				      type.getType()
				      )
			);
    }

    public void currentDirection(Genx86 generator)
	throws InvalidCodeException,IOException{
	constructor.register = register;
	index.register       = register + 1;
	
	String constructorReg = generator.addrRegName(constructor.register);
	String indexReg       = generator.intRegName(index.register);
	String errorCheckReg  = generator.intRegName(register+2);

	String listSize = Integer.toString(((ListType)(constructor.type)).len());

	//Ver NOTA
	String offsetReg      = generator.addrRegName(index.register);

	constructor.currentDirection(generator);

	generator.write(generator.save(index.register));
	generator.write(generator.save(register+2));

	index.tox86(generator);

	//Chequeo de errores: indice negativo
	generator.write(generator.cmp(indexReg,"0"));
	generator.write(generator.jl("halt"));

	//Chequeo de errores: indice fuera de rango
	generator.write(generator.movInt(errorCheckReg,listSize));
	generator.write(generator.sub(errorCheckReg,indexReg));
	generator.write(generator.cmp(errorCheckReg,"0"));
	generator.write(generator.jle("halt"));

	generator.write(generator.imul(indexReg,
				       Integer.toString(type.size())));

	generator.write(generator.add(constructorReg,
				      offsetReg));

	generator.write(generator.restore(register+2));
	generator.write(generator.restore(index.register));
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