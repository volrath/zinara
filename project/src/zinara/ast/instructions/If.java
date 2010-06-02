package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.instructions.IfCase;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;

import java.util.ArrayList;
import java.io.IOException;

public class If extends Instruction{
    private ArrayList cases; // Arraylist of IfCase's

    public If(ArrayList cs){
	this.cases = cs;
    }

    public ArrayList getCases(){
	return this.cases;
    }

    public String toString() {
	String ret = "<";
	for (int i = 0; i < cases.size(); i++)
	    ret += (Instruction)cases.get(i);
	return (ret + ">");
    }

    public void tox86(Genx86 generator) throws IOException,InvalidCodeException {
	IfCase ic;
	for (int i = 0; i < cases.size(); i++) {
	    ic = (IfCase)cases.get(i);
	    ic.register = register;
	    ic.nextInst = ((i != cases.size() - 1) ? generator.newLabel() : nextInst);
	    ic.completeIfNextInst = nextInst;
	    ic.tox86(generator);
	    if (i != cases.size() - 1) generator.writeLabel(ic.nextInst);
	}
    }
}
