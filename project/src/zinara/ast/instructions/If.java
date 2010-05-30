package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.instructions.IfCase;
import zinara.code_generator.Genx86;

import java.util.ArrayList;

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

    public void tox86(Genx86 generator){
	ifCase ic;
	for (int i = 0; i < cases.size(); i++) {
	    ic = (ifCase)cases.get(i);
	    ic.register = register;
	    ic.nextInst = ((i != cases.size() - 1) ? generator.newLabel() : nextInst);
	    ic.completeIfNextInst = nextInst;
	    ic.tox86(generator);
	    if (i != cases.size() - 1) generator.writeLabel(ic.nextInst);
	}
    }
}
