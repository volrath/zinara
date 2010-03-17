package zinara.exceptions;

public class InvalidDictionaryDeclaration extends Exception {
    String mistake;
    public InvalidDictionaryDeclaration() {
	super();
	mistake = "InvalidDictionaryDeclaration<unknown>";
    }

    public InvalidDictionaryDeclaration(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
