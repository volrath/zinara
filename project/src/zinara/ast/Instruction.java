package zinara.ast;

abstract class Instruction{}

class Asignation extends Instruction{
    private String id;
    private Expression expr;

    public Asignation(String name, Expression ex){
	this.id = name;
	this.expr = ex;
    }

    public String getName(){
	return this.id;
    }

    public Expression getExpression(){
	return this.expr;
    }
}
