package zinara.ast;

import zinara.ast.type.Type;

public class Param {
    private String id;
    private Type type;
    private boolean byValue;
    
    public Param(String i, Type t, boolean v){
	this.id = i;
	this.type = t;
	this.byValue = v;
    }

    public String getId(){
	return this.id;
    }

    public Type getType(){
	return this.type;
    }

    public boolean byValue(){
	return this.byValue;
    }
}
