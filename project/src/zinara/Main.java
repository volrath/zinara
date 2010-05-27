package zinara;

import zinara.ast.Program;
import zinara.code_generator.*;
import zinara.exceptions.*;
import zinara.lexer.*;
import zinara.parser.*;

import java.io.*;

public class Main {
    public static final boolean debug_parsing = true;

    public static boolean testStaticFail(String programName)
	throws ClassCastException, IdentifierAlreadyDeclaredException,
	       IdentifierNotDeclaredException, InvalidAssignationException,
	       TypeClashException, Exception {
	parser p = new parser(new Scanner(new FileReader(programName)));
	Program root = (Program)p.parse().value;
	return true;
    }

    public static String getStringAST(String programName) {
	try {
	    parser p = new parser(new Scanner(new FileReader(programName)));
	    Program root = (Program)p.parse().value;
	    return root.toString();
	} 
	catch (Exception e) {
	    e.printStackTrace();
	}
	return null;
    }

    public static String getStringSymTable(String programName) {
	try {
	    parser p = new parser(new Scanner(new FileReader(programName)));
	    Program root = (Program)p.parse().value;
	    return root.getSymTable().toString();
	} 
	catch (Exception e) {
	    e.printStackTrace();
	}
	return null;
    }

    public static void main(String argv[]) {
	try {	
	    parser p = new parser(new Scanner(new FileReader(argv[0])));
	    Program root;
	    String filename = argv[0];
	    String asmCodeFile = "../x86.asm";
		
	    if (debug_parsing)
		root = (Program)p.debug_parse().value;
	    else
		root = (Program)p.parse().value;

	    System.out.println("AST:      " + root + "\n");
	    System.out.println("SYMTABLE: " + root.getSymTable() + "\n");

	    System.out.println("Writing Assembler code to " + asmCodeFile + " ...");
	    Genx86 codeGenerator = new Genx86(Integer.parseInt(argv[1]), asmCodeFile);
	    codeGenerator.generateProgram(root);
	    System.out.println("... done.");
	} 
	catch (ClassCastException e) {
	    System.out.println("oops..., classcastE: " + e.toString());
	    e.printStackTrace();
	}
	catch (InvalidArchitectureException e) { System.out.println(e.getMessage());System.exit(1);}
	catch (IdentifierNotDeclaredException e) { System.out.println(e.getMessage());System.exit(1);}
	catch (IdentifierAlreadyDeclaredException e) { System.out.println(e.getMessage());System.exit(1);}
	catch (InvalidAssignationException e) { System.out.println(e.getMessage());System.exit(1);}
	catch (TypeClashException e) { System.out.println(e.getMessage());System.exit(1);}
	catch (Exception e) {
	    System.out.println("oops...");
	    e.printStackTrace();
	    System.out.println(e.getMessage());
	    System.exit(1);
	}
    }
}
