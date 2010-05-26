package zinara.ast.expression;

import zinara.ast.type.Type;
import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

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

    public void tox86(Genx86 generate) throws IOException {
	//generate.write(generate.mov(generate.current_reg(),"["+lvalue.tox86(generate)+"]"));
    }
}
