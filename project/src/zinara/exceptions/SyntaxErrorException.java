package zinara.exceptions;

public class SyntaxErrorException extends Exception {
    String mistake;

    public SyntaxErrorException() /* Maybe put the line of the previous declaration or something */ {
	super("Error de sintaxis");
	mistake = "Error de sintaxis";
    }

    public SyntaxErrorException(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
