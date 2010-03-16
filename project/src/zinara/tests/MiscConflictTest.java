package zinara.tests;

import zinara.Main;
import zinara.exceptions.InvalidAssignationException;

import junit.framework.*;

public class MiscConflictTest extends TestCase {
    private String STATIC_MC_DIR = "../test_files/misc_conflicts/";

    public MiscConflictTest(String name) { super(name); }

    public void testMiscConflict1() {
	try {
	    Main.testStaticFail(STATIC_MC_DIR + "mc1.zn");
	    fail("Should raise InvalidAssignationException");
	}
	catch (InvalidAssignationException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise InvalidAssignationException");
	}
    }
}
