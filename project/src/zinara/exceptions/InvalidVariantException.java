package zinara.exceptions;

public class InvalidVariantException extends Exception {
    String mistake;
    public InvalidVariantException() {
	super();
	mistake = "InvalidVariantException<unknown>";
    }

    public InvalidVariantException(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
