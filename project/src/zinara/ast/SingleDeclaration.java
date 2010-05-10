package zinara.ast;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.ast.expression.Identifier;

public class SingleDeclaration extends Declaration {
    private Type type;
    private String identifier;
    private Object value;
    private boolean variable;
    
    public SingleDeclaration(Type t, String id, Object v, boolean var) {
	this.type = t;
	this.identifier = id; this.value = v; this.variable = var;
    }

    public SingleDeclaration(Type t, Identifier id, Object v, boolean var) {
	this.type = t;
	this.identifier = id.getIdentifier(); this.value = v; this.variable = var;
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

    public String toString() {
	return "(Declaration: " + type + " " + identifier + " [" + (variable ? "VAR" : "CONST") + (value != null ? "="+value : "") +  "])";
    }

    public String tox86(Genx86 generate){
        return "";
    }
}
