package zinara.tests;

import zinara.Main;
import zinara.exceptions.*;

import junit.framework.*;

public class GrammarGoodTest extends TestCase {
    private String STATIC_TC_DIR = "../test_files/grammar_and_ast/";

    public GrammarGoodTest(String name) {
	super(name);
    }

    public void testIf() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "/struct_insts/g_if.zn");
	}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should not raise anything");
	}
    }

    public void testFor() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "/struct_insts/g_for.zn");
	}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should not raise anything");
	}
    }

    public void testWhile() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "/struct_insts/g_while.zn");
	}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should not raise anything");
	}
    }

    public void testCycle() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "/struct_insts/g_cycle.zn");
	}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should not raise anything");
	}
    }

    public void testDefs() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "/struct_insts/g_defs.zn");
	}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should not raise anything");
	}
    }

    public void testProgram() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "/struct_insts/g_program.zn");
	}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should not raise anything");
	}
    }

    public void testCompositeDecl() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "/struct_insts/g_composite_decl.zn");
	}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should not raise anything");
	}
    }

    public void testExprs() {
	try {
	    Main.testStaticFail(STATIC_TC_DIR + "/struct_exprs/g_exprs.zn");
	}
	catch (Exception e) { // any other exception
	    e.printStackTrace();
	    fail("Should not raise anything");
	}
    }
}
