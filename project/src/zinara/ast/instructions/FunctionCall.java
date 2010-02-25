package zinara.ast.instructions
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
