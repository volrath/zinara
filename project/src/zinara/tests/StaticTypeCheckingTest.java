package zinara.tests;

import zinara.Main;
import zinara.exceptions.TypeClashException;

import junit.framework.*;

public class StaticTypeCheckingTest extends TestCase {
    private String STATIC_TC_DIR = "../test_files/static_type_checking/";

    public StaticTypeCheckingTest(String name) {
	super(name);
    }

    public void testStaticTypeChecking1() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt1.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking2() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt2.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking3() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt3.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking4() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt4.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking5() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt5.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking6() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt6.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking7() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt7.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking8() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt8.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking9() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt9.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking10() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt10.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking11() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt11.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking12() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt12.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking13() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt13.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking14() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt14.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking15() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt15.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking16() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt16.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking17() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt17.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking18() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt18.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking19() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt19.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking20() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt20.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking21() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt21.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }

    public void testStaticTypeChecking22() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "bt22.zn");
	    fail("Should raise TypeClashException");
	}
	catch (TypeClashException success) {}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should raise TypeClashException");
	}
    }
}
