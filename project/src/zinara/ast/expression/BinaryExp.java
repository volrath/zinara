package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.code_generator.*;
import zinara.exceptions.TypeClashException;
import zinara.parser.sym;
import zinara.parser.parser;

import java.io.IOException;

public class BinaryExp extends Expression {
    public int operator;
    public Expression left;
    public Expression right;
    
    public BinaryExp (int o, Expression l, Expression r) throws TypeClashException {
	operator=o;
	left=l;
	right=r;
	type = parser.operators.check(this.operator, this.left.getType(), this.right.getType());
    }
    
    public Type getType() {
	return type;
    }

    public String toString() {
	return "("+left + " " + operator + " " + right+")" ;
    }

    public void tox86(Genx86 generate) throws IOException {
	String save;
	String restore;

	left.register = register;
	right.register = register + 1;
	
	left.tox86(generate);
	// Save and restore missing;
	//generate.write(generate.save());
	right.tox86(generate);

	if (type instanceof IntType)
	    generate.write(intOps(generate));
	else if (type instanceof FloatType)
	    generate.write(realOps(generate));
	else{
	    System.out.println("Tipo no implementado: "+operator);
	    System.exit(1);
	}

	// restore!
	//generate.write(generate.restore());
    }

    private String intOps(Genx86 generate){
	String code = "";

	if (operator == sym.PLUS){
	    code += generate.add(generate.regName(left.register),generate.regName(right.register));
	}
	else if (operator == sym.MINUS){
	    code += generate.sub(generate.regName(left.register),generate.regName(right.register));
	}
	else if (operator == sym.TIMES){
	    code += generate.imul(generate.regName(left.register),generate.regName(right.register));
	}
	else if (operator == sym.DIVIDE){
	    code += generate.idiv(generate.regName(left.register),generate.regName(right.register));
	}
	else if (operator == sym.MOD){
	    code += generate.imod(generate.regName(left.register),generate.regName(right.register));
	}
	else{
	    System.out.println("Operacion no implementada para enteros: "+operator);
	    System.exit(1);
	}
	
	return code;
    }

    private String realOps(Genx86 generate){
	String code = "";

	if (operator == sym.PLUS){
	    code += generate.fadd(generate.regName(left.register),generate.regName(right.register));
	}
	else if (operator == sym.MINUS){
	    code += generate.fsub(generate.regName(left.register),generate.regName(right.register));
	}
	else if (operator == sym.TIMES){
	    code += generate.fmul(generate.regName(left.register),generate.regName(right.register));
	}
	else if (operator == sym.DIVIDE){
	    code += generate.fdiv(generate.regName(left.register),generate.regName(right.register));
	}
	else{
	    System.out.println("Operacion no implementada para reales: "+operator);
	    System.exit(1);
	}
	
	return code;
    }

    public boolean isStaticallyKnown() { return left.isStaticallyKnown() && right.isStaticallyKnown(); }
}
