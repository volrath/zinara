package zinara.ast;

import java.io.IOException;

import zinara.ast.ASTNode;
import zinara.ast.type.Type;
import zinara.ast.expression.Expression;
import zinara.ast.expression.Identifier;
import zinara.ast.type.*;
import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidCodeException;
import zinara.symtable.*;

public class SingleDeclaration extends Declaration {
    private Type type;
    private String identifier;
    private Status status;
    private Expression expr;
    private SymTable symTable;
    
    public SingleDeclaration(Type t, String id, Expression expr, boolean var, SymTable st) throws TypeClashException {
	// Type checking first
	if (expr != null && !t.equals(expr.getType()))
	    throw new TypeClashException("Asignacion invalida: tipo de la expresion `" + expr + "`" + expr.getType() + " difiere del tipo " + t + " en la declaracion del identificador " + id);
	// ...
	this.type = t;
	this.identifier = id;
	this.expr = expr;
	this.symTable = st;
	if (var)
	    status = new Variable(); else status = new Constant(expr);
    }

    public SingleDeclaration(Type t, Identifier id, Expression expr, boolean var, SymTable st) throws TypeClashException {
	// Type checking first
	if (expr != null && !t.equals(expr.getType()))
	    throw new TypeClashException("Asignacion invalida: tipo de la expresion `" + expr + "`" + expr.getType() + " difiere del tipo " + t + " en la declaracion del identificador " + id.getIdentifier());
	// ...
	this.type = t;
	this.identifier = id.getIdentifier();
	this.expr = expr;
	this.symTable = st;
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

    public Expression getExpression() { return expr; }

    public Status getStatus() { return status; }

    public void setType(Type t) { this.type = t; }

    public String toString() {
	return "(Declaration: " + type + " " + identifier + " [" + status + "])";
    }

    public void tox86(Genx86 generator) throws IOException, InvalidCodeException {
	if (expr != null) {
	    String exprReg;
	    String lvalueReg;
	    SymValue sv = symTable.getSymbol(identifier);
	    
// 	    if (lvalue.type.equals(new BoolType())) {
// 		booleanAssignationToX86(generator);
// 		return;
// 	    }
	    
	    expr.register = register;
	    expr.tox86(generator);
	    
	    storeValue(generator, generator.regName(expr.register, sv.getType()));
	}
    }

    private void storeValue(Genx86 generator, String currentReg) throws IOException, InvalidCodeException {
	SymValue sv = symTable.getSymbol(identifier);
	Type type = sv.getType();
        //Si es un tipo numerico o boleano, se copian los contenidos
        if (type.getType() instanceof IntType)
            generator.write(generator.movInt(currentReg,
                                          "[" + generator.global_offset() +
                                          "+" + sv.getOffset() + 
                                          "]"));
        else if (type.getType() instanceof FloatType)
            generator.write(generator.movReal(currentReg,
                                          "[" + generator.global_offset() +
                                          "+" + sv.getOffset() + 
                                          "]"));
        else if (type.getType() instanceof BoolType)
            generator.write(generator.movBool(currentReg,
                                          "[" + generator.global_offset() +
                                          "+" + sv.getOffset() + 
                                          "]"));
        //Si es una lista o diccionario, devuelvo su direccion
        else if ((type.getType() instanceof ListType)||
		 (type.getType() instanceof DictType))
            generator.write(generator.movAddr(currentReg,
					      generator.global_offset()+
					      "+"+
					      Integer.toString(sv.getOffset())));
        else
            generator.write("Identificador para el tipo "+type.getType().toString()+" no implementado\n");
    }
}
