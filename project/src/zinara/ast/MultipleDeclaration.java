package zinara.ast;

import java.io.IOException;
import java.util.ArrayList;

import zinara.ast.ASTNode;
import zinara.ast.expression.Identifier;
import zinara.ast.instructions.MultipleAssignation;
import zinara.ast.type.Type;
import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidCodeException;
import zinara.symtable.SymTable;

public class MultipleDeclaration extends Declaration {
    public ArrayList declarations; // arraylist of SingleDeclaration
    private Type type;

    public MultipleDeclaration(ArrayList ds) { this.declarations = ds; }

    public MultipleDeclaration(ArrayList ids, Type type, SymTable st) throws TypeClashException {
	ArrayList declarations = new ArrayList();
	for (int  i = 0; i < ids.size(); i++)
	    declarations.add(new SingleDeclaration(type, ((String)ids.get(i)), null, true, st));
	this.declarations = declarations;
	this.type = type;
    }

    public MultipleDeclaration(MultipleAssignation asigs, Type type, boolean var, SymTable st) throws TypeClashException {
	ArrayList declarations = new ArrayList();
	for (int i = 0; i < asigs.assignations.size(); i++)
	    declarations.add(new SingleDeclaration(type, (Identifier)(asigs.get(i).getLValue()), asigs.get(i).getExpression(), var, st));
	this.declarations = declarations;
	this.type = type;
    }

    public boolean isSingle(){
	return false;
    }

    public boolean add(SingleDeclaration d) { return this.declarations.add(d); }

    public SingleDeclaration get(int i) { return (SingleDeclaration)this.declarations.get(i); }

    public int size(){
	return this.declarations.size();
    }
    
    public Type getType(){
	return this.type;
    }

    public String toString() {
	String ret = "";
	SingleDeclaration currentDeclaration;
	for (int i = 0; i < declarations.size(); i++)
	    ret += " " + declarations.get(0);
	return "MultipleDeclaration:" + ret;
    }

    public void tox86(Genx86 generate)
	throws IOException,InvalidCodeException{
	for (int i = 0; i < declarations.size(); i++)
	    ((SingleDeclaration)declarations.get(i)).tox86(generate);
    }
}
