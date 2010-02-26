package zinara.ast;

import java.util.ArrayList;

public class MultipleDeclaration extends Declaration {
    public ArrayList declarations;

    public MultipleDeclaration(ArrayList ds) { this.declarations = ds; }

    public boolean isSingle(){
	return false;
    }

    public boolean add(SingleDeclaration d) { return this.declarations.add(d); }

    public SingleDeclaration get(int i) { return (SingleDeclaration)this.declarations.get(i); }

    public int size(){
	return this.declarations.size();
    }
}
