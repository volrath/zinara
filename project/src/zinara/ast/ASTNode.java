package zinara.ast;

import zinara.ast.expression.Expression;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

public abstract class ASTNode {
    public String code;
    public int register;
    public abstract void tox86(Genx86 generate)
	throws IOException,InvalidCodeException;

    public void boolValue(Genx86 generate,  Expression expr,
				 String ret, String reg)
	throws IOException,InvalidCodeException{
	String yesLabel = generate.newLabel();
	String noLabel  = generate.newLabel();
	expr.yesLabel = yesLabel;
	expr.noLabel = noLabel;
	expr.tox86(generate);
	generate.writeLabel(yesLabel);
	generate.write(generate.movBool(reg,"1"));
	generate.write(generate.jump(ret));
	generate.writeLabel(noLabel);
	generate.write(generate.movBool(reg,"0"));
    }
}