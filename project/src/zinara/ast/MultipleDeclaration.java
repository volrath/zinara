package zinara.ast;

import java.util.ArrayList;

import zinara.ast.instructions.MultipleAssignation;
import zinara.ast.type.Type;
import zinara.ast.type.ConstantType;

public class MultipleDeclaration extends Declaration {
    public ArrayList declarations; // arraylist of SingleDeclaration

    public MultipleDeclaration(ArrayList ds) { this.declarations = ds; }

    public MultipleDeclaration(ArrayList ids, Type type) {
	ArrayList declarations = new ArrayList();
	for (int  i = 0; i < ids.size(); i++)
	    declarations.add(new SingleDeclaration(type, ((String)ids.get(i)), null, false));
	this.declarations = declarations;
    }

    // Constant type!!!
    public MultipleDeclaration(MultipleAssignation asigs, Type type) {
	ArrayList declarations = new ArrayList();
	for (int i = 0; i < asigs.assignations.size(); i++)
	    declarations.add(new SingleDeclaration(new ConstantType(type,asigs.get(i).getExpression()), asigs.get(i).getId(), asigs.get(i).getExpression(), false));
	this.declarations = declarations;
    }

    public boolean isSingle(){
	return false;
    }

    public boolean add(SingleDeclaration d) { return this.declarations.add(d); }

    public SingleDeclaration get(int i) { return (SingleDeclaration)this.declarations.get(i); }

    public int size(){
	return this.declarations.size();
    }

    public String toString() {
	String ret = "";
	SingleDeclaration currentDeclaration;
	for (int i = 0; i < declarations.size(); i++)
	    ret += " " + declarations.get(0);
	return "MultipleDeclaration:" + ret;
    }
}
