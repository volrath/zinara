package zinara;

import zinara.parser.*;
import zinara.lexer.*;

import java.io.*;

public class Main {
    public static void main(String argv[]) {
	try {
	    parser p = new parser(new Scanner(new FileReader(argv[0])));
	    Object result = p.debug_parse().value;
	} catch (Exception e) {
	    System.out.println("oops... shit");
	    e.printStackTrace();
	}
    }
}
