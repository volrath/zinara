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

    public String tox86(Genx86 generate) throws IOException{
// 	String symName;
// 	SymValue symVal;

// 	int total_size = 0;

// 	//Calculo de la cantidad de espacio para las variables globales
// 	//Se le asignan los offset a cada varaible global
// 	while (len >= 0){
// 	    symName = (String)symbols[len];
// 	    //Actualizacion del valor (lo remuevo, modifico y vuelvo a insertar)
// 	    symVal = (SymValue)symtable.deleteSymbol(symName);
// 	    symVal.setDesp(total_size);
// 	    total_size += symVal.getSize();
// 	    symtable.addSymbol(symName,symVal);

// 	    --len;
// 	}
	
	Iterator keyIt = symtable.keySet().iterator();
	String identifier;
	SymValue symValue;

	int total_size = 0;
	while(keyIt.hasNext()) {
	    identifier = (String)keyIt.next();
	    symValue = symtable.getSymbol(identifier);
	    total_size += symValue.type.size;
	}

	//HEADER DEL .ASM
	//  El espacio para variables, texto de las funciones
	//  y el comienzo del texto del main se crean aca
	code += generate.data(generate.data_offset(),total_size);
	code += generate.main_text_header();
	generate.write(code);

	//Codigo del main
	this.main.tox86(generate);

	//El programa termina con codigo de terminacion 0 (exito)
	code = generate.exit_syscall(0);
	generate.write(code);

	generate.closeFile();

	return "";
    }
}