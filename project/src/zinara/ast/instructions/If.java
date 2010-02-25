package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import java.util.ArrayList;

public class If extends Instruction{
    private ArrayList cases;

    public If(ArrayList cs){
	this.cases = cs;
    }

    public ArrayList getCases(){
	return this.cases;
    }
}
