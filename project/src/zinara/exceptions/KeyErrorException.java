package zinara.exceptions;

public class KeyErrorException extends Exception {
    String mistake;
    public KeyErrorException() {
	super();
	mistake = "KeyErrorException<unknown>";
    }

    public KeyErrorException(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
