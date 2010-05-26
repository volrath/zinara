package zinara.ast.instructions;
import zinara.code_generator.*;

import zinara.ast.expression.Expression;
import java.util.ArrayList;

public class If extends Instruction{
    private ArrayList cases; // Arraylist of... ???  wtf?! IfCase's?!

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

    public void tox86(Genx86 generate){
    }
}
