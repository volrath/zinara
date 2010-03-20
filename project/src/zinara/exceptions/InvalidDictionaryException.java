package zinara.exceptions;

public class InvalidDictionaryException extends Exception {
    String mistake;
    public InvalidDictionaryException() {
	super();
	mistake = "InvalidDictionaryException<unknown>";
    }

    public InvalidDictionaryException(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
