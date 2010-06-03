package zinara.ast;

import java.io.IOException;

import zinara.ast.ASTNode;
import zinara.ast.type.Type;
import zinara.ast.expression.Expression;
import zinara.ast.expression.Identifier;
import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;
import zinara.symtable.Status;
import zinara.symtable.Constant;
import zinara.symtable.Variable;

public class SingleDeclaration extends Declaration {
    private Type type;
    private String identifier;
    private Status status;
    
    public SingleDeclaration(Type t, String id, Expression expr, boolean var) throws TypeClashException {
	// Type checking first
	if (expr != null && !t.equals(expr.getType()))
	    throw new TypeClashException("Asignacion invalida: tipo de la expresion `" + expr + "`" + expr.getType() + " difiere del tipo " + t + " en la declaracion del identificador " + id);
	// ...
	this.type = t;
	this.identifier = id;
	if (var)
	    status = new Variable(); else status = new Constant(expr);
    }

    public SingleDeclaration(Type t, Identifier id, Expression expr, boolean var) throws TypeClashException {
	// Type checking first
	if (expr != null && !t.equals(expr.getType()))
	    throw new TypeClashException("Asignacion invalida: tipo de la expresion `" + expr + "`" + expr.getType() + " difiere del tipo " + t + " en la declaracion del identificador " + id.getIdentifier());
	// ...
	this.type = t;
	this.identifier = id.getIdentifier();
	if (var) status = new Variable(); else status = new Constant(expr);
    }

    public boolean isSingle(){
	return true;
    }

    public Type getType(){
	return this.type;
    }

    public String getId(){
	return this.identifier;
    }

    public Status getStatus() { return status; }

    public void setType(Type t) { this.type = t; }

    public String toString() {
	return "(Declaration: " + type + " " + identifier + " [" + status + "])";
    }

    public void tox86(Genx86 generate) throws IOException {
	// "SingleDeclaration NO IMPLEMENTADA";
    }
}
