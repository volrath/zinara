package zinara.code_generator;

import zinara.ast.*;
import zinara.ast.instructions.*;
import zinara.ast.expression.*;
import zinara.symtable.*;
import zinara.exceptions.InvalidArchitectureException;
import zinara.parser.sym;

import java.io.FileWriter;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.File;
import java.util.ArrayList;

public class Genx86{
    private String[] regs;
    private String stackp;
    private String framep;
    private String stackAlig;
    private int n_regs;
    private int next_reg;
    private int bits;
    private BufferedWriter file;
    //LinkedList offsetStack;
    //int currentOffset;

    public Genx86(int bits, File file) throws InvalidArchitectureException, IOException{
	if (bits == 64){
	    regs = new String[14];
	    regs[0] = "eax";
	    regs[1] = "ebx";
	    regs[2] = "ecx";
	    regs[3] = "edx";
	    regs[4] = "esi";
	    regs[5] = "edi";
	    regs[6] = "r8d";
	    regs[7] = "r9d";
	    regs[8] = "r10d";
	    regs[9] = "r11d";
	    regs[10] = "r12d";
	    regs[11] = "r13d";
	    regs[12] = "r14d";
	    regs[13] = "r15d";

	    stackp = "rsp";
	    framep = "rbp";
	    stackAlig = "8";

	    n_regs = 14;
	}
	else if (bits == 32){
	    regs = new String[6];
	    regs[0] = "eax";
	    regs[1] = "ebx";
	    regs[2] = "ecx";
	    regs[3] = "edx";
	    regs[4] = "esi";
	    regs[5] = "edi";

	    stackp = "esp";
	    framep = "ebp";
	    stackAlig = "4";

	    n_regs = 6;
	}
	else
	    throw new InvalidArchitectureException(bits); 
	
	next_reg = 0;
	this.bits = bits;
	this.file = new BufferedWriter(new FileWriter(file));

	if (this.bits == 64)
	    this.file.write("BITS 64\n");
    }

    public void write(String thing) throws IOException{
	file.write(thing);
    }

    public void closeFile() throws IOException{
	file.close();
    }

    public String free_reg(){
	return regs[next_reg%n_regs];
    }

    public String stack_pointer(){
	return stackp;
    }

    public String frame_pointer(){
	return framep;
    }

    public String get_reg(int reg){
	return regs[reg%n_regs];
    }

    public String next_reg() {
	this.next_reg += 1;
	// if (next_reg >= n_regs){
	//     if (this.bits == 32){
	// 	save = "push "+get_reg(next_reg)+"\n";
	// 	restore = "pop "+get_reg(next_reg)+"\n";
	//     }
	//     else {
	// 	save = "mov [rsp],"+get_reg(next_reg)+"\nsub rsp,8\n";
	// 	restore = "mov "+get_reg(next_reg)+",[rsp]\nadd rsp,8\n";
	//     }	    
	// }
	
	return regs[next_reg%n_regs];
    }

    public void prevs_regs(int n) {
	String exception = "";
	this.next_reg -= n;
	exception = regs[next_reg];
    }

    public String global_data(int data_size){
	return "section .bss\n   glob: resb "+data_size+"\n";
    }

    public String main_text_header(){
	return "section .text\n   global _start\n   _start:\n";
    }

    public String pushw (String thing){
	String code = "";

	if (this.bits == 32)
	    return "push "+thing+"\n";
	else{
	    code += mov("[rsp]",thing,"");
	    code += mov("[rsp+4]","0h","dword");
	    code += sub("rsp",stackAlig);
	    return code;
	}
    }

    public String pushq (String thing){
	if (this.bits == 64)
	    return "mov [rsp],"+thing+"\nsub rsp,"+stackAlig+"\n";
	else{
	    System.out.println("pushq en 32 bits");
	    System.exit(1);
	}
	return "";
    }

    public String pop (String thing){
	String code = "";

	if (this.bits == 32)
	    return "pop "+thing+"\n";
	else{
	    return "add rsp,"+stackAlig+"\nmov "+thing+",[rsp]\n";
	}
    }


    public String mov(String dst, String orig, String size_mod){
	return "mov "+size_mod+" "+dst+","+orig+"\n";
    }

    public String add(String dst, String op2){
	return "add "+dst+","+op2+"\n";
    }

    public String sub(String dst, String op2){
	return "sub "+dst+","+op2+"\n";
    }

    public String imul(String dst, String op2){
	return "imul "+dst+","+op2+"\n";
    }

    public String idiv(String dividend, String diviser){
	String code = "";

	code += pushw("eax"); //Parte baja del dividendo
	code += pushw("ebx"); //Divisor
	code += pushw("edx"); //Parte alta del dividendo

	//Aqui pongo los argumentos en los registros
	code += pushw(dividend);
	code += pushw(diviser);
	code += pop("ebx");
	code += pop("eax");

	code += mov("edx","0h","dword");
	//Limpio la parte alta porque no se va a usar

	code += "idiv ebx\n";
	code += pop("edx");//Restauro registros 
	code += pop("ebx");//Restauro registros 

	//If en caso de que el registro donde debe quedar la division
	//esa el mismo eax, no lo puedo sobreescribir
	if (dividend.compareTo("eax") == 0)
	    code += add(this.stackp,this.stackAlig);
	else{
	    code += mov(dividend,"eax","");
	    code += pop("eax");
	}
	return code;
    }

    public String save_print_regs(){
	String code = "";
	if (this.bits == 32){
	    code += pushw("eax");//Codigo del syscall
	    code += pushw("ebx");//Descriptor
	    code += pushw("ecx");//Direccion del string
	    code += pushw("edx");//Cantidad a imprimir
	}
	else{
	    code += pushq("rax");//Codigo del syscall
	    code += pushq("rdi");//Descriptor
	    code += pushq("rsi");//Direccion del string
	    code += pushq("rdx");//Cantidad a imprimir
	    code += pushq("rcx");//Registro que destruye el kernel
	    code += pushq("r11");//Registro que destruye el kernel
	}
	return code;
    }

    public String restore_print_regs(){
	String code = "";
	if (this.bits == 32){
	    code += pop("edx");//Codigo del syscall
	    code += pop("ecx");//Descriptor
	    code += pop("ebx");//Direccion del string
	    code += pop("eax");//Cantidad a imprimir
	}
	else{
	    code += pop("r11");//Codigo del syscall
	    code += pop("rcx");//Descriptor
	    code += pop("rdx");//Direccion del string
	    code += pop("rsi");//Cantidad a imprimir
	    code += pop("rdi");//Registro que destruye el kernel
	    code += pop("rax");//Registro que destruye el kernel
	}
	return code;
    }

    //El addr, si es un label, debe venir sin corchetes...duh
    public String setup_print(String addr, String desc, String bytes){
	String code = "";

	if (this.bits == 32){
	    code += "mov eax,4\n"; //Codigo de sys_write 32 bits
	    code += "mov ebx,"+desc+"\n"; //Descriptor a donde escribir (1=stdout)
	    code += "mov ecx,"+addr+"\n"; //Direccion donde comienza el valor a imprimir
	    code += "mov edx,"+bytes+"\n"; //Cantidad de bytes que se van a imprimir
	}
	else{
	    code += "mov rax,1\n"; //Codigo de sys_write 64 bits
	    code += "mov rdi,"+desc+"\n"; //Descriptor a donde escribir (1=stdout)
	    code += "mov rsi,"+addr+"\n"; //Direccion donde comienza el valor a imprimir
	    code += "mov rdx,"+bytes+"\n"; //Cantidad de bytes que se van a imprimir
	}
	return code;
    }

    public String exit_syscall(int exit_code){
	if (this.bits == 64)
	    return "mov rax,60\nmov rdi,"+exit_code+"\nsyscall\n";	    
	else
	    return "mov eax,1\nmov ebx,"+exit_code+"\nint 80h\n";
    }

    public String syscall(){
	if (this.bits == 32)
	    return "int 80h\n";
	else
	    return "syscall\n";
    }

    public String/*void*/ tox86(/*FileHandle,*/Program program) throws InvalidArchitectureException{
	SymTable symtable = program.getSymTable();
	Main main = program.getMain();
	//ArrayList declarations = program.getDeclarations();

	String code = "";
	int len;
	
	Object[] symbols = symtable.getSymbols();
	len = symbols.length-1;
	String symName;
	SymValue symVal;

	int total_size = 0;

	//Calculo de la cantidad de espacio para las variables globales
	//Se le asignan los offset a cada varaible global
	while (len >= 0){
	    symName = (String)symbols[len];
	    //Actualizacion del valor (lo remuevo, modifico y vuelvo a insertar)
	    symVal = (SymValue)symtable.deleteSymbol(symName);
	    symVal.setDesp(total_size);
	    total_size += symVal.getSize();
	    symtable.addSymbol(symName,symVal);

	    --len;
	}
	
	if (this.bits == 64){
	    code += "BITS 64\n";
	}
	code += "section .bss\n   glob: resb "+total_size+"\n";
	code += "section .text\n   global _start\n   _start:\n";
	code += tox86(main);
	code += "mov eax,1\nmov ebx,0\nint 80h\n";

	return code;
    }

    public String/*void*/ tox86(/*FileHandle,*/Main main) throws InvalidArchitectureException{
	CodeBlock codeB = main.getCode();
	return tox86(codeB);
    }
        
    public String/*void*/ tox86(/*FileHandle,*/MultipleDeclaration multipledeclaration){
	return "";
    }
    
    public String/*void*/ tox86(/*FileHandle,*/SingleDeclaration singledeclaration){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/Break _break){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/CallInst callinst){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/CodeBlock codeblock) throws InvalidArchitectureException{
	ArrayList block = codeblock.getBlock();
	String code = "";

	for (int i = 0; i < block.size(); i++)
	    code += tox86((Instruction)block.get(i));
	return code;
    }

    public String/*void*/ tox86(/*FileHandle,*/Continue _continue){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/CycleCase cyclecase){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/Cycle cycle){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/DecInst decinst){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/For _for){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/IfCase ifcase){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/If _if){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/SingleAssignation singleassignation){
	LValue lvalue = singleassignation.getLValue();
	Expression exp = singleassignation.getExpression();

	String code = "";
	String lvalueDir;
	int expReg;
	
	expReg = next_reg;
	code += tox86(exp);
       	lvalueDir = tox86(lvalue);

	code += "mov ["+lvalueDir+"],"+get_reg(expReg)+"\n";
	
	//Liberar registro del lvalue si lo uso

	return code;
    }

    public String/*void*/ tox86(/*FileHandle,*/MultipleAssignation multipleassignation){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/Print print) throws InvalidArchitectureException{
	//Por ahora se asume que todas las expresiones son numeros enteros
	Expression exp = print.getExpression();
	int expReg;
	String code = "";

	expReg = next_reg;
	code += tox86(exp);

	//"Transformo" a ASCII
	code += "add "+get_reg(expReg)+",48\n";

	//Seteo la los registros para la llamada
	if (bits == 32){
	    //Salvo los registros que va a utilizar la llamada al sistema
	    code += pushw("eax");
	    code += pushw("ebx");
	    code += pushw("ecx");
	    code += pushw("edx");

	    code += "mov [esp],"+get_reg(expReg)+"\n"; //Valor a imprimir
	    code += "mov eax,4\n"; //Codigo de sys_write
	    code += "mov ebx,1\n"; //Descriptor a donde escribir (1=stdout)
	    code += "mov ecx,esp\n"; //Direccion donde comienza el valor a imprimir
	    code += "mov edx,4\n"; //Cantidad de bytes que se van a imprimir
	    code += "int 80h\n"; //Llamada al sistema

	    //Restauro los registros
	    code += pop("edx");
	    code += pop("ecx");
	    code += pop("ebx");
	    code += pop("eax");
	}
	else if (bits == 64){
	    //Salvo los registros que va a utilizar la llamada al sistema
	    code += pushw("rdi");
	    code += pushw("rsi");
	    code += pushw("rcx");
	    code += pushw("r11");
	    code += pushw("rdx");

	    code += "mov [rsp],"+get_reg(expReg)+"\n"; //Valor a imprimir
	    code += "mov dword [rsp+4],0h\n";  //Como estoy usando los registros e_x, limpio la parte alta de los 64 bits
	    code += "mov rax,1\n"; //Codigo de sys_write
	    code += "mov rdi,1\n"; //Descriptor a donde escribir (1=stdout)
	    code += "mov rsi,rsp\n"; //Direccion donde comienza el valor a imprimir
	    code += "mov rdx,4\n"; //Cantidad de bytes que se van a imprimir
	    code += "syscall \n"; //Llamada al sistema

	    //Restauro los registros
	    code += pop("rdx");
	    code += pop("r11");
	    code += pop("rcx");
	    code += pop("rsi");
	    code += pop("rdi");
	}
	    	    
	return code;
    }

    public String/*void*/ tox86(/*FileHandle,*/Return _return){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/While _while){
	return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/BinaryExp binaryexp){
	String code = "";
	int regs_used = 1;
	
	Expression exp1 = binaryexp.left;
	Expression exp2 = binaryexp.right;
	String exp1Reg = next_reg();
	String exp2Reg;
	int opCode = binaryexp.operator;
	
	code += tox86(exp1);

	exp2Reg = next_reg();
	code += tox86(exp2);

	if (opCode == sym.PLUS){
	    code += "add "+exp1Reg+","+exp2Reg+"\n";
	}
	else if (opCode == sym.MINUS){
	    code += "sub "+exp1Reg+","+exp2Reg+"\n";
	}
	else if (opCode == sym.TIMES){
	    code += "imul "+exp1Reg+","+exp2Reg+"\n";
	}
	else if (opCode == sym.DIVIDE){
	    code += pushw("eax"); //Parte baja del dividendo
	    code += pushw("ebx"); //Divisor
	    code += pushw("edx"); //Parte alta del dividendo
	    code += pushw(exp1Reg);
	    code += pushw(exp2Reg);
	    code += pop("ebx");		    
	    code += pop("eax");		    
	    code += "mov dword edx,0h\n";
	    code += "idiv ebx\n";
	    code += pop("edx");
	    code += pop("ebx");
	    //If en caso de que el registro donde debe quedar la division
	    //esa el mismo eax, no lo puedo sobreescribir
	    if (exp1Reg.compareTo("eax") == 0)
		code += "add "+this.stackp+","+this.stackAlig+"\n";
	    else{
		code += "mov "+exp1Reg+",eax\n";
		code += pop("eax");
	    }
	}
	else
	    System.exit(1);

	next_reg -= regs_used;
        return code;
    }

    public String/*void*/ tox86(/*FileHandle,*/CallExp callexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/CharExp charexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/DictExp dictexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/FalseExp falseexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/FloatExp floatexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/Identifier identifier){
	return "glob+"+identifier.getSymValue().getDesp();
    }

    public String/*void*/ tox86(/*FileHandle,*/LValueContents lvaluecontents){
	LValue lval = lvaluecontents.getLValue();
	return "mov "+get_reg(next_reg)+",["+tox86(lval)+"]\n";
    }

    public String/*void*/ tox86(/*FileHandle,*/ListExp listexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/IntegerExp integerexp){
	return "mov "+get_reg(next_reg)+","+integerexp.toString()+"\n";	
    }

    public String/*void*/ tox86(/*FileHandle,*/LValueDict lvaluedict){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/LValueList lvaluelist){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/LValueTuple lvaluetuple){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/ReadExp readexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/StringExp stringexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/TrueExp trueexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/TupleExp tupleexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/UnaryExp unaryexp){
        return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/Instruction inst)throws InvalidArchitectureException{
	if (inst instanceof SingleAssignation){
	    return tox86((SingleAssignation) inst);
	}
	else if (inst instanceof Print){
	    return tox86((Print) inst);
	}
	else
	    return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/Expression exp){
	if (exp instanceof IntegerExp){
	    return tox86((IntegerExp) exp);
	}
	else if (exp instanceof LValue){
	    return tox86((LValue) exp);
	}
	else if (exp instanceof LValueContents){
	    return tox86((LValueContents) exp);
	}
	else if (exp instanceof BinaryExp){
	    return tox86((BinaryExp) exp);
	}
	else
	    return "";
    }

    public String/*void*/ tox86(/*FileHandle,*/LValue lvalue){
	if (lvalue instanceof Identifier){
	    return tox86((Identifier) lvalue);
	}
	else
	    return "";
    }
}