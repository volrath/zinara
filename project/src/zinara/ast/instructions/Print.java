package zinara.ast.instructions;

import zinara.ast.expression.Expression;

class Print extends Instruction{
    private Expression expr;

    public Print(Expression ex){
	this.expr = ex;
    }

    public Expression getExpression(){
	return this.expr;
    }
}