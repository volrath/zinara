package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.exceptions.TypeClashException;

public class LValueContents extends Expression {
    private LValue lvalue;
    
    public LValueContents(LValue lv){
	this.lvalue = lv;
    }
    
    public LValue getLValue(){ return this.lvalue; }

    public void setLValue(LValue lv) { this.lvalue = lv; }

    public Type getType() throws TypeClashException{
	return this.lvalue.getType();
    }

    public String toString(){
	return this.lvalue.toString();
    }

    public String tox86(Genx86 generate){
	return generate.mov(generate.current_reg(),"["+lvalue.tox86(generate)+"]");
    }
}
