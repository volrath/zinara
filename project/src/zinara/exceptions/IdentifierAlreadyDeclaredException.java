package zinara.exceptions;

public class IdentifierAlreadyDeclaredException extends Exception {
    String mistake;
    public IdentifierAlreadyDeclaredException() {
	super();
	mistake = "unknown";
    }

    public IdentifierAlreadyDeclaredException(String id) /* Maybe put the line of the previous declaration or something */ {
	super("El identificador " + id + " ya ha sido declarado en la línea tal, columna tal");
	mistake = "El identificador " + id + " ya ha sido declarado en la línea tal, columna tal";
    }

    public String getMessage() { return mistake; }
}
