package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.code_generator.*;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

public class Print extends Instruction{
    private Expression expr;

    public Print(Expression ex){
	this.expr = ex;
    }

    public Expression getExpression(){
	return this.expr;
    }

    public String toString() {
	return "<Print " + expr + ">";
    }

    public void tox86(Genx86 generate) throws IOException, InvalidCodeException{
	// Por ahora se asume que todas las expresiones son numeros enteros
	//de un solo digito.
	String code = "";
	String expReg = generate.regName(register,expr.type);

	expr.tox86(generate);

	//"Transformo" a ASCII
	code += generate.add(expReg,"48");

	code += generate.save_print_regs();

	//Necesita ser generico, esperando que asm_io funcione
	code += generate.movInt("["+generate.stack_pointer()+"]",expReg);
	// Pongo el valor de la expresion en la pila, ya que la llamada
        //sys_write necesita que el String este en memoria.
	
	code += generate.setup_print(generate.stack_pointer(),"1","4");
	code += generate.syscall();
	code += generate.restore_print_regs();
	    	    
	generate.write(code);
    }
}