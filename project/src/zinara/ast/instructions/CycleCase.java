package zinara.ast.instructions;

import zinara.ast.expression.Expression;

public class CycleCase{
    private Expression expr;
    private CodeBlock code;

    public CycleCase(CodeBlock cb, Expression ex){
	this.code = cb;
	this.expr = ex;
    }

    public CodeBlock getCode(){
	return this.code;
    }

    public Expression getExpression(){
	return this.expr;
    }
}
