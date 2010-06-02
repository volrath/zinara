package zinara.exceptions;

public class InvalidCodeException extends Exception {
    String mistake;
    public InvalidCodeException() {
	super();
	mistake = "InvalidCodeException<unknown>";
    }

    public InvalidCodeException(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
