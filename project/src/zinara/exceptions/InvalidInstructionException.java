package zinara.exceptions;

public class InvalidInstructionException extends Exception {
    String mistake;

    public InvalidInstructionException() /* Maybe put the line of the previous declaration or something */ {
	super("Instruccion invalida");
	mistake = "Instruccion invalida";
    }

    public InvalidInstructionException(String err) {
	super(err);
	mistake = err;
    }

    public String getMessage() { return mistake; }
}
