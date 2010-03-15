package zinara.exceptions;

public class InvalidAssignationException extends Exception {
    String mistake;

    public InvalidAssignationException() /* Maybe put the line of the previous declaration or something */ {
	super("Asignacion invalida");
	mistake = "Asignacion invalida";
    }

    public String getMessage() { return mistake; }
}
