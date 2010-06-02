package zinara.ast;

import zinara.ast.ASTNode;
import zinara.ast.instructions.CodeBlock;
import zinara.code_generator.*;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

public class Main extends ASTNode {
    CodeBlock code;
    
    public Main(CodeBlock c) {
	this.code = c;
    }
    
    public CodeBlock getCode(){
	return this.code;
    }

    public String toString() { return "(Main: " + code + ")"; }

    public void tox86(Genx86 generate) throws IOException,InvalidCodeException{
	this.code.register = register;
	this.code.tox86(generate);
    }
}
