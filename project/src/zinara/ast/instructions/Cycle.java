package zinara.ast.instructions;
import zinara.code_generator.*;

import zinara.ast.expression.Expression;
import java.util.ArrayList;

public class Cycle extends Instruction{
    private CodeBlock optional;
    private ArrayList cases; // arraylist of CycleCase's
    private boolean has_optional;

    public Cycle(ArrayList cs, CodeBlock cb){
	this.cases = cs;
	this.optional = cb;
	this.has_optional = !(cb==null);
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

    public String toString() {
	return "<G-LOOP>";
    }

    public void tox86(Genx86 generate){
    }
}
