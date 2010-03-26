package zinara.exceptions;

public class InvalidAccessException extends Exception {
    String mistake;

    public InvalidAccessException() /* Maybe put the line of the previous declaration or something */ {
	super("Acceso invalida");
	mistake = "Acceso invalida";
    }

    public InvalidAccessException(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
