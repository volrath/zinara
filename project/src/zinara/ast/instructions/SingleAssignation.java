package zinara.ast.instructions;

import zinara.ast.expression.Expression;

public class SingleAssignation extends Assignation {
    private String id;
    private Expression expr;

    public boolean isSingle(){
	return true;
    }

    public SingleAssignation(String name, Expression ex){
	this.id = name;
	this.expr = ex;
    }

    public String getId(){
	return this.id;
    }

    public Expression getExpression(){
	return this.expr;
    }
}
