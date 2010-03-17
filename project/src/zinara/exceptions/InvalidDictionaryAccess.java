package zinara.exceptions;

public class InvalidDictionaryAccess extends Exception {
    String mistake;
    public InvalidDictionaryAccess() {
	super();
	mistake = "InvalidDictionaryAccess<unknown>";
    }

    public InvalidDictionaryAccess(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
