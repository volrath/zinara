package zinara.ast.expression;
import zinara.code_generator.*;

public abstract class LValue extends Expression {
    public String tox86(Genx86 generate){
        return "";
    }
}
