package zinara.ast;
import zinara.code_generator.*;

import zinara.ast.instructions.CodeBlock;

import java.io.IOException;

public class Main {
    CodeBlock code;
    
    public Main(CodeBlock c) {
	this.code = c;
    }
    
    public CodeBlock getCode(){
	return this.code;
    }

    public String toString() { return "(Main: " + code + ")"; }

    public String tox86(Genx86 generate) throws IOException{
	this.code.tox86(generate);
	return "";
    }
}
