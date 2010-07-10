package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.expression.BooleanExp;
import zinara.ast.expression.Identifier;
import zinara.code_generator.*;
import zinara.ast.type.Type;
import zinara.ast.type.IntType;
import zinara.ast.type.FloatType;
import zinara.ast.type.CharType;
import zinara.ast.type.BoolType;
import zinara.ast.type.StringType;
import zinara.ast.expression.LValue;
import zinara.ast.expression.StringExp;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

public class Print extends Instruction{
    private Expression expr;

    public Print(Expression ex) throws TypeClashException {
	Type eType = ex.getType();
	if (!(eType instanceof StringType) &&
	    !(eType instanceof CharType) &&
	    !(eType instanceof IntType) &&
	    !(eType instanceof FloatType) &&
	    !(eType instanceof BoolType))
	    throw new TypeClashException("La expresion " + ex + " no es imprimible");
	this.expr = ex;
    }

    public Expression getExpression(){
	return this.expr;
    }

    public String toString() {
	return "<Print " + expr + ">";
    }

    public void tox86(Genx86 generate)
	throws IOException,InvalidCodeException{
	expr.register = register;
	String expReg = generate.addrRegName(expr.register);
	String expRegBool = generate.boolRegName(expr.register);

	// if (expr.type.equals(new BoolType())){
	//     String ret = generate.newLabel();
	//     boolValue(generate,expr,ret,expRegBool);
	//     generate.writeLabel(ret);
	// }
	if (expr instanceof BooleanExp){
	    String ret = generate.newLabel();
	    boolValue(generate,expr,ret,expRegBool);
	    generate.writeLabel(ret);
	}
	else if (!(expr instanceof StringExp)&&
		 (expr.type instanceof StringType)){
	    System.out.println("noasfa2");
	    ((LValue)expr).currentDirection(generate);
	}
	else{
	    expr.tox86(generate);
	}

	generate.write(generate.push("rdi"));
	generate.write(generate.push("rax"));
	generate.write(generate.push("rcx"));
	generate.write(generate.push("r11"));

	generate.write(generate.mov("rdi",expReg));
	if (expr.type instanceof IntType){
	    generate.write("call print_int\n");
	}
	else if (expr.type instanceof BoolType){
	    generate.write("call print_int\n");
	}
	else if (expr.type instanceof FloatType){
	    generate.write("call print_float\n");
	}
	else if (expr.type instanceof CharType){
	    generate.write("call print_char\n");
	}
	else if (expr.type instanceof StringType){
	    generate.write("call print_string\n");
	}
	else{
	    generate.write("print de "+expr.type+" no implementado");
	    System.out.println("====================");
	    System.out.println("print de "+expr.type+" no implementado");
	    System.out.println("====================");
	}
	generate.write("call print_nl\n");
	
	generate.write(generate.pop("r11"));
	generate.write(generate.pop("rcx"));
	generate.write(generate.pop("rax"));
	generate.write(generate.pop("rdi"));
    }
}
