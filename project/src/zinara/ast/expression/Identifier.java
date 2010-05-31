package zinara.ast.expression;

import zinara.ast.type.BoolType;
import zinara.ast.type.FloatType;
import zinara.ast.type.IntType;
import zinara.ast.type.ListType;
import zinara.ast.type.Type;
import zinara.code_generator.Genx86;
import zinara.symtable.*;

import java.io.IOException;

public class Identifier extends LValue {
    private String identifier;
    private SymTable symtable;

    public Identifier (String id, SymTable st) {
	identifier = id;
	symtable = st;
    }

    public String getIdentifier() { return identifier; }
    public SymTable getSymTable() { return symtable; }
    public SymValue getSymValue(){
	return symtable.getSymbol(identifier);
    }

    public Type getType() {
	if (type != null) return type;
	type = symtable.getSymValueForId(identifier).getType();
	return type;
    }
    public String toString() { return identifier; }

    public void tox86(Genx86 generator) throws IOException {
	// if (isExpression() && !getSymValue().isKnownConstant())
	//     generator.write(getSymValue().knownConstant(generator));

	// generator.write(generator.mov(generator.regName(register),
	// 			      generator.global_offset()+
	// 			      "+"+
	// 			      Integer.toString(getSymValue().getOffset())));
	String reg = generator.regName(register);

	//Si es un tipo numerico o boleano, se copian los contenidos
	if ((type.getType() instanceof IntType)||
	    (type.getType() instanceof FloatType)||
	    (type.getType() instanceof BoolType))
	    generator.write(generator.mov(reg,
					  "[" + generator.global_offset() +
					  "+" + getSymValue().getOffset() + 
					  "]"));
	//Si es una lista, devuelvo su direccion
	else if (type.getType() instanceof ListType)
	    generator.write(generator.mov(reg,
					  generator.global_offset()+
					  "+"+
					  Integer.toString(getSymValue().getOffset())));
	else
	    generator.write("Identificador para el tipo "+type.getType().toString()+" no implementado\n");	    

	// generator.write(generator.add(generator.regName(register),
	// 			      generator.global_space()));

	// if (isExpression()) {
	//     if (isBool())
	// 	writeBooleanExpression(generator);
	//     else
	// 	writeExpression(generator);
	// }
    }

    public String currentDirection(Genx86 generator) {
	return "[" + generator.global_offset() + "+" + getSymValue().getOffset() + "]";
    }
}
