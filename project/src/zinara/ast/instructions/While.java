package zinara.ast.instructions;
import zinara.code_generator.*;

import zinara.ast.expression.Expression;

public class While extends Instruction{
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

    public String toString() { return "While " + expr + ": " + code + ">"; }

    public String tox86(Genx86 generate){
        return "";
    }
}
