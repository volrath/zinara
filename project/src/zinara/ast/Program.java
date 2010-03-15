package zinara.ast;

import java.util.ArrayList;

import zinara.symtable.SymTable;

public class Program {
    private SymTable symtable;
    private Main main;
    private ArrayList declarations;
    
    public Program(SymTable st, Main m, ArrayList ds) {
	symtable = st;
	main = m;
	declarations = ds;
    }

    public Program(SymTable st, Main m) {
	symtable = st;
	main = m;
	declarations = null;
    }

    public Main getMain() { return this.main; }

    public SymTable getSymTable() { return symtable; }

    public String toString() { return "(Program: " + main + ")"; }

}