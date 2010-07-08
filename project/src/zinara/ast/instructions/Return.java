package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.type.Type;
import zinara.code_generator.*;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

public class Return extends Instruction{
    private Expression expr;

    public Return(Expression ex){
	this.expr = ex;
    }

    public Expression getExpression(){
	return this.expr;
    }

    public String toString() {
	return "<Return " + expr + ">";
    }

    public void tox86(Genx86 generator)
	throws IOException,InvalidCodeException{
	expr.register = register;

	//Type exprType = expr.getType();
	Type exprType = expr.type;
	String expReg = generator.regName(expr.register,exprType);

	String asm = "";
	String frame_p = generator.frame_pointer();
	String stack_p = generator.stack_pointer();
	String word_size = Integer.toString(generator.word_size());

	/*En x86, el resultado de las funciones
	  se deja en rax(64bits)/eax(32bits)
	*/
	String ax = generator.regName(0,exprType);

	expr.tox86(generator);

	//Resultado en el registro ax
	asm += generator.mov(ax,expReg);

	//Se desempila todo que esta despues de la cadena dinamica
	asm += generator.mov(stack_p,frame_p);

	//Se restaura la cadena dinamica
	asm += generator.mov(frame_p,"["+stack_p+"]");
	
	//Se pone el stack pointer a apuntar a la direccion de retorno
	asm += generator.add(stack_p,word_size);

	//Return
	asm += generator.ret();

	generator.write(asm);
    }
}