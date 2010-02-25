package zinara.ast.instructions;

import zinara.ast.expression.Expression;

public class For extends Instruction{
    private Expression expr;
    private CodeBlock code;
    private String id;

    public For(String i, CodeBlock cb, Expression ex){
	this.id = i;
	this.code = cb;
	this.expr = ex;
    }

    public String getId(){
	return this.id;
    }

    public CodeBlock getCode(){
	return this.code;
    }

    public Expression getExpression(){
	return this.expr;
    }
}
