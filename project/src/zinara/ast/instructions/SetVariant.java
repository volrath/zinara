package zinara.ast.instructions;
import zinara.code_generator.*;

import zinara.ast.expression.Expression;
import zinara.ast.expression.LValue;

public class SetVariant extends Instruction{
    public LValue lvalue;
    public String variant;

    public SetVariant(LValue lv, String var) {
	lvalue  = lv;
	variant = var;
    }

    public String toString() {
	return "<SetVariant " + lvalue + " as " + variant +">";
    }

    public void tox86(Genx86 generate){
    }
}