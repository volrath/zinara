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

    public String tox86(Genx86 generate) throws IOException{
	// Por ahora se asume que todas las expresiones son numeros enteros
	//de un solo digito.
	String code = "";
	String expReg = generate.current_reg();

	code += expr.tox86(generate);

	//"Transformo" a ASCII
	code += generate.add(expReg,"48");

	code += generate.save_print_regs();

	code += generate.mov("["+generate.stack_pointer()+"]",expReg);
	//Pongo el valor de la expresion en la pila.
	
	code += generate.setup_print(generate.stack_pointer(),"1","4");
	code += generate.syscall();
	code += generate.restore_print_regs();
	    	    
	generate.write(code);
	return "";
    }
}