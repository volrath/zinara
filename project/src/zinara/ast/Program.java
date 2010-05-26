package zinara.ast;

import zinara.code_generator.Genx86;
import zinara.symtable.SymTable;
import zinara.symtable.SymValue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;

public class Program extends ASTNode {
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

    public void tox86(Genx86 generator) throws IOException {}
}