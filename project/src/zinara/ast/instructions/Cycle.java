package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import java.util.ArrayList;

public class Cycle extends Instruction{
    private CodeBlock optional;
    private ArrayList cases;
    private boolean has_optional;

    public Cycle(ArrayList cs, CodeBlock cb){
	this.cases = cs;
	this.optional = cb;
	if (cb == null)
	    has_optional=false;
	else
	    has_optional=true;
    }

    public ArrayList getCases(){
	return this.cases;
    }

    public CodeBlock getOptional(){
	return this.optional;
    }

    public boolean has_optional(){
	return this.has_optional;
    }
}
