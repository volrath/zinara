package zinara.ast.instructions;
import zinara.code_generator.*;

import zinara.ast.expression.Expression;

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

    public void tox86(Genx86 generator) throws IOException{
	// Por ahora se asume que todas las expresiones son numeros enteros
	//de un solo digito.
	String code = "";
	expr.register = register;

	expr.tox86(generator);

	//"Transformo" a ASCII
	code += generator.add(generator.regName(register),"48");

	code += generator.save_print_regs();

	code += generator.mov("["+generator.stack_pointer()+"]",generator.regName(register));
	// Pongo el valor de la expresion en la pila, ya que la llamada
        //sys_write necesita que el String este en memoria.
	
	code += generator.setup_print(generator.stack_pointer(),"1","4");
	code += generator.syscall();
	code += generator.restore_print_regs();
	    	    
	generator.write(code);
    }
}