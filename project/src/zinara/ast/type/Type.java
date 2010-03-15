package zinara.ast.type;

public abstract class Type {
    public boolean equals(Type other) {
	/*
	  Basic Types
	*/
	if ((this instanceof IntType && other instanceof IntType) || 
	    (this instanceof FloatType && other instanceof FloatType) ||
	    (this instanceof CharType && other instanceof CharType) ||
	    (this instanceof BoolType && other instanceof BoolType))
	    return true;
	else {
	    /*
	      Composed Types
	     */
	    //if (this instanceof ListType)
	    return false;
	}
    }

    public abstract String toString();
}
