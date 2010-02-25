package zinara.ast.instructions
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

class Print extends Instruction{
    private Expression expr;

    public Print(Expression ex){
	this.expr = ex;
    }

    public Expression getExpression(){
	return this.expr;
    }
}

class Read extends Instruction{
    public Read(){}
}

class While extends Instruction{
    private Expression expr;
    private CodeBlock code;

    public While(CodeBlock cb, Expression ex){
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

class Return extends Instruction{
    private Expression expr;

    public Return(Expression ex){
	this.expr = ex;
    }

    public Expression getExpression(){
	return this.expr;
    }
}

class FunctionCall extends Instruction{
    private ExpressionList expr_list;
    private String func_name;

    public While(String fn, ExpressionList exl){
	this.func_name = fn;
	this.expr_list = exl;
    }

    public String getFuncion(){
	return this.func_name;
    }

    public ExpressionList getExpressionList(){
	return this.expr_list;
    }
}
