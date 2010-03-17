package zinara.exceptions;

public class SyntaxErrorException extends Exception {
    String mistake;
    public SyntaxErrorException() {
	super();
	mistake = "SyntaxErrorException<unknown>";
    }

    public SyntaxErrorException(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
