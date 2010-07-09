package zinara.ast.expression;

import zinara.ast.type.CharType;
import zinara.ast.type.StringType;
import zinara.ast.type.Type;
import zinara.code_generator.*;
import zinara.exceptions.InvalidCodeException;

import java.io.IOException;

public class StringExp extends Expression {
    public String value;
    public StringExp(String v) { value = v; type = new StringType(); }
    public Type getType() { return type; }
    public String toString() { return "\"" + value + "\""; }

    public void tox86(Genx86 generate)
	throws IOException,InvalidCodeException {
	String code = "";

	String reg = generate.regName(register,new CharType());
	String addrReg = generate.addrRegName(register);
	char ch;

	code += generate.pushChar("0");//End of string
	for (int i = value.length()-2; i >= 1; --i){
	    ch = value.charAt(i);
	    code += generate.pushChar(generate.toASCII(ch));
	}
	
	code += generate.movAddr(addrReg,generate.stack_pointer());
	
	generate.write(code);
    }

    public boolean isStaticallyKnown() { return true; }

    public Object staticValue() { return value; };
}
