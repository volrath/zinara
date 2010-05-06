package zinara.ast.expression;
import zinara.code_generator.*;

import java.util.ArrayList;

import zinara.ast.type.Type;
import zinara.ast.type.IntType;

public class CallExp extends Expression {
    private String name;
    private ArrayList arguments; // arraylist of ????
   
    public CallExp (String nm, ArrayList s) { 
	this.name = nm; 
	arguments = s;
    }

    public Type getType() { return new IntType(); }

    public String toString() { return name + "(" + arguments + ")"; }

    public String tox86(Genx86 generate){
        return "";
    }
}
