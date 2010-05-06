package zinara.ast.instructions;
import zinara.code_generator.*;

import zinara.ast.expression.Expression;
import zinara.symtable.SymTable;
import zinara.symtable.SymValue;
import zinara.ast.type.Type;

public class For extends Instruction{
    private Expression expr;
    public CodeBlock code;
    private String i; //Iteration variable name

    public For(String i, Expression ex, CodeBlock cb){
	this.i = i;
	this.code = cb;
	this.expr = ex;
    }

    public String getI(){
	return this.i;
    }

    public CodeBlock getCode(){
	return this.code;
    }

    public Expression getExpression(){
	return this.expr;
    }

    public String toString() {
	return "<For " + i + " in " + expr + ": " + code + ">";
    }   

    public String tox86(Genx86 generate){
        return "";
    }
}