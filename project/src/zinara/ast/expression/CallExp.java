package zinara.ast.expression;

import java.util.ArrayList;

public class CallExp extends Expression {
   public String name;
   public ArrayList arguments;
   public CallExp ( String nm, ArrayList s ) { name=nm; arguments=s; }
}
