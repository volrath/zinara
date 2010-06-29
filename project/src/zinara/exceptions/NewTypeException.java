package zinara.exceptions;

public class NewTypeException extends Exception {
    String mistake;
    public NewTypeException() {
	super();
	mistake = "NewTypeException<unknown>";
    }

    public NewTypeException(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
