package zinara.ast.expression;

public class UnaryExp extends Expression {
   public int operator;
   public Expression operand;

   public UnaryExp ( int o, Expression e ) { operator=o; operand=e; }
}