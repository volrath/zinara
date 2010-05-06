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
	if (i < 0 || i >= ((TupleType)c.getType()).size())
	    throw new KeyErrorException("El indice " + i + " es mayor al tamano de la tupla (" + ((TupleType)c.getType()).size() + ")");

	constructor = c;
	index = i;
    }

    public Type getType() throws TypeClashException {
	return ((TupleType)constructor.getType()).get(index);
    }
    public String toString() { return constructor + "[" + index + "]"; }

    public String tox86(Genx86 generate){
        return "";
    }
}