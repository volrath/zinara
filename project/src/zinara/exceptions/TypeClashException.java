package zinara.exceptions;

public class TypeClashException extends Exception {
    String mistake;
    public TypeClashException() {
	super();
	mistake = "unknown";
    }

    public TypeClashException(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
