package zinara.exceptions;

public class IdentifierNotDeclaredException extends Exception {
    String mistake;
    public IdentifierNotDeclaredException() {
	super();
	mistake = "unknown";
    }

    public IdentifierNotDeclaredException(String id) /* Maybe put the line of the previous declaration or something */ {
	super("El identificador " + id + " no ha sido declarado en el alcance actual");
	mistake = "El identificador " + id + " no ha sido declarado en el alcance actual";
    }

    public String getMessage() { return mistake; }
}
