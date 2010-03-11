package zinara.ast.expression;

import java.util.ArrayList;

public class CallExp extends Expression {
    private String name;
    private ArrayList arguments;
   
    public CallExp (String nm, ArrayList s) { 
	this.name = nm; 
	arguments = s;
    }

    public Integer getType() { return new Integer(0); }
}
