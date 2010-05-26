package zinara.ast.instructions;
import zinara.code_generator.*;

import zinara.ast.expression.Expression;

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

    public void tox86(Genx86 generate){
    }
}