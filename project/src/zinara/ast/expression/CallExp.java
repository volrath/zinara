package zinara.ast.expression;

import java.util.ArrayList;

import zinara.ast.type.Type;
import zinara.ast.type.IntType;

public class CallExp extends Expression {
    private String name;
    private ArrayList arguments;
   
    public CallExp (String nm, ArrayList s) { 
	this.name = nm; 
	arguments = s;
    }

    public Type getType() { return new IntType(); }
}
