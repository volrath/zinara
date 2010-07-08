package zinara.ast;

import zinara.ast.type.RoutineType;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;
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

    public ArrayList declarations(){
	return this.declarations;
    }

    public void tox86(Genx86 generator)
	throws IOException, InvalidCodeException{
	// Generacion de subrutinas
	if (declarations != null)
	    for (int i = 0; i < declarations.size(); i++){
		Declaration d = (Declaration)(declarations.get(i));
		if (d.getType() instanceof RoutineType)
		    d.tox86(generator);
	    }

	// Reserva de espacio y etiqueta del main
	generator.generateHeader(symtable);

	// Asignacion de declaraciones
	if (declarations != null)
	    for (int i = 0; i < declarations.size(); i++){
		Declaration d = (Declaration)(declarations.get(i));
		if (! (d.getType() instanceof RoutineType))
		    d.tox86(generator);
	    }

	main.tox86(generator);
    }
}