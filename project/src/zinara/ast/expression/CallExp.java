package zinara.ast.expression;

public class CallExp extends Expression {
   public String name;
   public ExpressionList arguments;
   public CallExp ( String nm, ExpressionList s ) { name=nm; arguments=s; }
}
