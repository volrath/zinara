package zinara.ast.expression;

public class UnaryExp extends Expression {
   public String operator;
   public Expression operand;
   public UnaryExp ( String o, Expression e ) { operator=o; operand=e; }
}