package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.StringType;
import zinara.ast.type.Type;

public class StringExp extends Expression {
    public String value;
    public StringExp(String v) { value = v; type = new StringType(); }
    public Type getType() { return type; }
    public String toString() { return "\"" + value + "\""; }

    public void tox86(Genx86 generate){
	
    }

    public boolean isStaticallyKnown() { return true; }

    public Object staticValue() { return value; };
}
