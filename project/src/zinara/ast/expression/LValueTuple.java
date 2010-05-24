package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.ast.type.TupleType;
import zinara.exceptions.KeyErrorException;
import zinara.exceptions.TypeClashException;

public class LValueTuple extends LValue {
    private LValue constructor;
    private int index;

    // requires c.getType() be of Tuple type
    public LValueTuple(LValue c, int i)
	throws KeyErrorException, TypeClashException {
	// check if i is between the bounds of the type
	if (i < 0 || i >= ((TupleType)(c.getType().getType())).size())
	    throw new KeyErrorException("El indice " + i + " es mayor al tamano de la tupla (" + ((TupleType)c.getType()).size() + ")");

	constructor = c;
	index = i;
    }

    public Type getType() throws TypeClashException {
	if (type != null) return type;
	type = ((TupleType)(constructor.getType().getType())).get(index);
	return type;
    }
    public String toString() { return constructor + "[" + index + "]"; }

    public String tox86(Genx86 generate){
        return "";
    }
}