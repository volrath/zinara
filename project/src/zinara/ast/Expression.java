abstract class Expression {}

class IntegerExp extends Expression {
   public int value;
   public IntegerExp ( int n ) { value=n; }
}

class TrueExp extends Expression {
   public TrueExp () {}
}
class FalseExp extends Expression {
   public FalseExp () {}
}

class IdentifierExp extends Expression {
   public String value;
   public VariableExp ( String n ) { value=n; }
}

class BinaryExp extends Expression {
   public String operator;
   public Expression left;
   public Expression right;

   public BinaryExp (String o, Expression l, Expression r) { operator=o; left=l; right=r; }
}

class UnaryExp extends Expression {
   public String operator;
   public Expression operand;
   public UnaryExp ( String o, Expression e ) { operator=o; operand=e; }
}

class ExpressionList {
   public Expression head;
   public ExpressionList next;
   public ExpressionList ( Expression h, ExpressionList n ) { head=h; next=n; }
}

class CallExp extends Expression {
   public String name;
   public ExpressionList arguments;
   public CallExp ( String nm, ExpressionList s ) { name=nm; arguments=s; }
}

// class ProjectionExp extends Expression {
//    public Expression value;
//    public String attribute;
//    public ProjectionExp ( Expression v, String a ) { value=v; attribute=a; }
// }

// class RecordElements {
//    public String attribute;
//    public Expression value;
//    public RecordElements next;
//    public RecordElements ( String a, Expression v, RecordElements el )
//           { attribute=a; value=v; next=el; }
// }
// class RecordExp extends Expression {
//     public RecordElements elements;
//     public RecordExp ( RecordElements el ) { elements=el; }
// }