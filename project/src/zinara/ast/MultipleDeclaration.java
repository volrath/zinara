package zinara.ast;

import java.util.ArrayList;

public class MultipleDeclaration extends Declaration {
    public ArrayList declarations;
    public boolean isSingle = false;

    public MultipleDeclaration(ArrayList ds) { this.declarations = ds; }
    public boolean add(SingleDeclaration d) { return this.declarations.add(d); }
    public SingleDeclaration get(int i) { return (SingleDeclaration)this.declarations.get(i); }
}
