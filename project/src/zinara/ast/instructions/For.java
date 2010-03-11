package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.symtable.SymTable;
import zinara.symtable.SymValue;
import zinara.ast.type.Type;

public class For extends Instruction{
    private Expression expr;
    public CodeBlock code;
    private String i;

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
}
