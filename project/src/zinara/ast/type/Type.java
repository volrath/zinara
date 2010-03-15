package zinara.ast.type;

public abstract class Type {
    public boolean equals(Type other) {
	/*
	  Basic Types
	*/
	if ((this.getType() instanceof IntType && other.getType() instanceof IntType) || 
	    (this.getType() instanceof FloatType && other.getType() instanceof FloatType) ||
	    (this.getType() instanceof CharType && other.getType() instanceof CharType) ||
	    (this.getType() instanceof BoolType && other.getType() instanceof BoolType))
	    return true;
	else {
	    /*
	      Composed Types
	     */
	    //if (this instanceof ListType)
	    return false;
	}
    }

    public abstract Type getType();
    public abstract String toString();
}
