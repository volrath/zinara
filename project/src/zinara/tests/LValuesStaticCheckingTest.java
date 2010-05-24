package zinara.tests;

import zinara.Main;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidAccessException;

import junit.framework.*;

public class LValuesStaticCheckingTest extends TestCase {
    private String STATIC_TC_DIR = "../test_files/lvalues_static_checking/";

    public LValuesStaticCheckingTest(String name) {
	super(name);
    }

    public void testLValuesStaticChecking1() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls1.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking2() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls2.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking3() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls3.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking4() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls4.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking5() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls5.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking6() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls6.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking7() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls7.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking8() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls8.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking9() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls9.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking10() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls10.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking11() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls11.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking12() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls12.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking13() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls13.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking14() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls14.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking15() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls15.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking16() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls16.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking17() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls17.zn");
	    fail("Should raise TypeClashException");
	}
	catch (InvalidAccessException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking18() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls18.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testLValuesStaticChecking19() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "ls19.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }
}
