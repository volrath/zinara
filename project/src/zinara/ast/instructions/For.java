package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.ast.Symtable;
import zinara.ast.SymConst;
import zinara.ast.type.Type;

public class For extends Instruction{
    private Expression expr;
    private CodeBlock code;
    private String i;
    private Symtable st;

    public For(String i, CodeBlock cb, Expression ex, Symtable s, Type t){
	this.i = i;
	this.code = cb;
	this.expr = ex;
	this.st = new Symtable(s);
	st.addSymbol(i,new SymConst(ex,t,false));
    }

    public String getI(){
	return this.i;
    }

    public CodeBlock getCode(){
	return this.code;
    }

    public Expression getExpression(){
	return this.expr;
    }
}
