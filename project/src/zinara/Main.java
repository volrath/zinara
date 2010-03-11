package zinara;

import zinara.parser.*;
import zinara.lexer.*;
import zinara.ast.Program;

import java.io.*;

public class Main {
    public static final boolean debug_parsing = true;

    public static void main(String argv[]) {
	try {
	    parser p = new parser(new Scanner(new FileReader(argv[0])));
	    Program root;
	    if (debug_parsing)
		root = (Program)p.debug_parse().value;
	    else
		root = (Program)p.parse().value;
	    System.out.println(root);
	} 
	catch (ClassCastException e) {
	    System.out.println("oops..., classcastE: "+e.toString());
	    e.printStackTrace();
	}
	catch (Exception e) {
	    System.out.println("oops...");
	    e.printStackTrace();
	}
    }
}
