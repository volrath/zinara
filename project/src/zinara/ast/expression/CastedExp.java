package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;
import zinara.parser.parser;

import java.io.IOException;

public class CastedExp extends Expression {
    public Type cast;
    public Expression expr;
    
    public CastedExp (Type c, Expression e) throws TypeClashException {
	cast=c;
	expr=e;
	type = parser.operators.check(parser.operators.cast, this.expr.getType(), c);
    }
    
    public Type getType() throws TypeClashException {
	return type;
    }

    public String toString() {
	return "(<"+cast+"> "+expr+")";
    }

    public void tox86(Genx86 generator)
	throws IOException,InvalidCodeException{
	String code = "";
	String reg = generator.regName(register,expr.type);
	String stack_p = generator.stack_pointer();

	expr.tox86(generator);  //Se genera la expresion
	code += generator.push(reg,expr.type);
	if (expr.type instanceof IntType){
	    if (cast instanceof FloatType){
		code += generator.fild("["+stack_p+"]");//Se guarda la expresion en la pila de flotantes
		code += generator.fst("["+stack_p+"]"); //Se saca como flotante
		code += generator.fninit();  //Se reinicializa la pila de flotantes
		code += generator.pop(reg,expr.type);
		generator.write(code); 
	    }
	}
	else if (expr.type instanceof FloatType){
	    if (cast instanceof IntType){
		code += generator.fld("["+stack_p+"]"); //Se guarda la expresion en la pila de flotantes
		code += generator.fist("["+stack_p+"]");//Se saca como entero
		code += generator.fninit();  //Se reinicializa la pila de flotantes
		code += generator.pop(reg,expr.type);
		generator.write(code); 
	    }
	}
	else{
	    System.out.println("Codigo de CastedExp para "+expr.type+"->"+cast+" no generado");
	    return;
	}
    }

    public boolean isStaticallyKnown() { return expr.isStaticallyKnown(); }

    public Object staticValue() {
	return null;
    }
}