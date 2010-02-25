package zinara.ast;

import java.util.ArrayList;

public class Program {
    private Main main;
    private ArrayList declarations;
    
    public Program(Main m, ArrayList ds){
	main = m;
	declarations = ds;
    }

    public Program(Main m) {
	main = m;
	declarations = null;
    }

    public Main getMain() { return this.main; }
}