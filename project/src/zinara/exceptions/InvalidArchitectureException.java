
package zinara.exceptions;

public class InvalidArchitectureException extends Exception {
    String mistake;

    public InvalidArchitectureException(int err) {
	super(Integer.toString(err));
	mistake = Integer.toString(err);
    }

    public String getMessage() { return mistake; }
}
