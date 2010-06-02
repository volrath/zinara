package zinara.ast.instructions;

import zinara.ast.expression.BooleanExp;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

public class While extends Instruction{
    private BooleanExp expr;
    private CodeBlock code;

    public While(CodeBlock cb, BooleanExp ex){
	this.code = cb;
	this.expr = ex;
    }

    public CodeBlock getCode(){
	return this.code;
    }

    public BooleanExp getExpression(){
	return this.expr;
    }

    public String toString() { return "While " + expr + ": " + code + ">"; }

    public void tox86(Genx86 generator) throws IOException,InvalidCodeException {
	expr.yesLabel = generator.newLabel();
	expr.noLabel  = nextInst;

	code.register = register;
	code.nextInst = generator.newLabel();

	generator.write(generator.jump(code.nextInst));
	generator.writeLabel(expr.yesLabel);
	code.tox86(generator);
	generator.writeLabel(code.nextInst);
	expr.tox86(generator);
    }
}
