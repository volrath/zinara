package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;
import zinara.parser.parser;

import java.io.IOException;

public class CastedExp extends Expression {
    public Type cast;
    public Expression exp;
    
    public CastedExp (Type c, Expression e) {
	cast=c;
	exp=e;
    }
    
    public Type getType() throws TypeClashException {
	return parser.operators.check(parser.operators.cast, this.exp.getType(), null);
    }

    public String toString() {
	return "(<"+cast+"> "+exp+")";
    }

    public void tox86(Genx86 generate) throws IOException{
        //return "Codigo de CastedExp NO GENERADO";
    }
}