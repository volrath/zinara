package zinara.ast;

import zinara.ast.type.Type;

public class SingleDeclaration extends Declaration {
    private Type type;
    private String identifier;
    private Object value;
    private boolean variable;
    
    public SingleDeclaration(Type t, String id, Object v, boolean var) {
	this.type = t;
	this.identifier = id; this.value = v; this.variable = var;
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

    public Object getValue(){
	return this.value;
    }    

    public boolean isVariable(){
	return this.variable;
    }

    public void setType(Type t) { this.type = t; }
    public void setVariable(boolean var) { this.variable = var; }
}
