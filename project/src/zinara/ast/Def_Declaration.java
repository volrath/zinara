package zinara.ast;

import zinara.ast.type.Type;

public class Def_Declaration extends Declaration {
    private Type type;
    private String name;
    private Symtable table;
    
    public Def_Declaration(Type t, String id, Symtable st) {
	this.type = t;
	this.name = id; 
	this.table = st;
    }

    public Type getType(){
	return this.type;
    }

    public String getName(){
	return this.name;
    }

    public Symtable getTable(){
	return this.table;
    }
}
