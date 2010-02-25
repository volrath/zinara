package zinara.ast.expression;

public class ExpressionList {
   public Expression head;
   public ExpressionList next;
   public ExpressionList ( Expression h, ExpressionList n ) { head=h; next=n; }
}
