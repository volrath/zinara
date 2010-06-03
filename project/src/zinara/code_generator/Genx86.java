package zinara.code_generator;

import zinara.ast.*;
import zinara.ast.instructions.*;
import zinara.ast.expression.*;
import zinara.exceptions.InvalidArchitectureException;
import zinara.exceptions.InvalidCodeException;
import zinara.parser.sym;
import zinara.symtable.SymTable;
import zinara.symtable.SymValue;
import zinara.ast.type.*;

import java.io.FileWriter;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.File;
import java.util.ArrayList;
import java.util.Iterator;

public class Genx86{
    private String[] regs;
    private String[] dwordRegs;
    private String[] byteRegs;
    private String stackp;
    private String framep;
    private String stackAlig; //Alineamiento de la pila
    private String global_offset;
    
    private int n_regs;
    private int next_reg;
    private int bits;
    private int labelCounter = 0;

    private BufferedWriter file;

    private String save;
    private String restore;

    public Genx86(int bits, String fileName) throws InvalidArchitectureException, IOException{
	if (bits == 64){
	    regs = new String[14];
	    dwordRegs = new String[14];
	    byteRegs = new String[14];

	    regs[0] = "rax";
	    regs[1] = "rbx";
	    regs[2] = "rcx";
	    regs[3] = "rdx";
	    regs[4] = "rsi";
	    regs[5] = "rdi";
	    regs[6] = "r8";
	    regs[7] = "r9";
	    regs[8] = "r10";
	    regs[9] = "r11";
	    regs[10] = "r12";
	    regs[11] = "r13";
	    regs[12] = "r14";
	    regs[13] = "r15";

	    dwordRegs[0] = "eax";
	    dwordRegs[1] = "ebx";
	    dwordRegs[2] = "ecx";
	    dwordRegs[3] = "edx";
	    dwordRegs[4] = "esi";
	    dwordRegs[5] = "edi";
	    dwordRegs[6] = "r8d";
	    dwordRegs[7] = "r9d";
	    dwordRegs[8] = "r10d";
	    dwordRegs[9] = "r11d";
	    dwordRegs[10] = "r12d";
	    dwordRegs[11] = "r13d";
	    dwordRegs[12] = "r14d";
	    dwordRegs[13] = "r15d";

	    byteRegs[0] = "al";
	    byteRegs[1] = "bl";
	    byteRegs[2] = "cl";
	    byteRegs[3] = "dl";
	    byteRegs[4] = "sil";
	    byteRegs[5] = "dil";
	    byteRegs[6] = "r8b";
	    byteRegs[7] = "r9b";
	    byteRegs[8] = "r10b";
	    byteRegs[9] = "r11b";
	    byteRegs[10] = "r12b";
	    byteRegs[11] = "r13b";
	    byteRegs[12] = "r14b";
	    byteRegs[13] = "r15b";

	    stackp = "rsp";
	    framep = "rbp";
	    stackAlig = "8";

	    n_regs = 14;
	}
	else if (bits == 32){
	    regs = new String[6];
	    byteRegs = new String[6];

	    regs[0] = "eax";
	    regs[1] = "ebx";
	    regs[2] = "ecx";
	    regs[3] = "edx";
	    regs[4] = "esi";
	    regs[5] = "edi";

	    byteRegs[0] = "al";
	    byteRegs[1] = "bl";
	    byteRegs[2] = "cl";
	    byteRegs[3] = "dl";
	    byteRegs[4] = "sil";
	    byteRegs[5] = "dil";

	    stackp = "esp";
	    framep = "ebp";
	    stackAlig = "4";

	    n_regs = 6;
	}
	else
	    throw new InvalidArchitectureException(bits); 
	
	global_offset = "glob";

	next_reg = 0;
	this.bits = bits;
	save = null;
	restore = null;

	file = new BufferedWriter(new FileWriter(new File(fileName)));

	file.write("%include \"asm_io.inc\"\n");
	    
	if (this.bits == 64)
	    this.file.write("BITS 64\n");
    }

    public void generateProgram(Program program) throws IOException,InvalidCodeException {
	generateHeader(program.getSymTable());

	// Generate code for all of its functions
	// ...
	// And then main
	program.getMain().register = 0;
	program.getMain().getCode().nextInst = "halt";

	program.getMain().tox86(this);

	// Exits the program
	writeLabel(program.getMain().getCode().nextInst);
	exitSyscall(0);
	closeFile();
    }

    public void generateHeader(SymTable symtable) throws IOException,InvalidCodeException {
	String identifier;
	SymValue symValue;

	// First set space for global variables
 	Iterator keyIt = symtable.keySet().iterator();
	int total_size = 0;
	while(keyIt.hasNext()) {
	    identifier = (String)keyIt.next();
	    symValue = symtable.getSymbol(identifier);
	    if (symValue.type.size() == 0) continue;
	    symValue.setOffset(total_size);
	    total_size += symValue.type.size();
	}
	// then for main variables
	SymTable mainSymTable = symtable.getSon(symtable.getSons().size()-1);
 	keyIt = mainSymTable.keySet().iterator();
	while(keyIt.hasNext()) {
	    identifier = (String)keyIt.next();
	    symValue = mainSymTable.getSymbol(identifier);
	    if (symValue.type.size() == 0) continue;
	    symValue.setOffset(total_size);
	    total_size += symValue.type.size();
	}

	// .ASM HEADER
	//  El espacio para variables, texto de las funciones
	//  y el comienzo del texto del main se crean aca
	write(reserve_space_str(global_offset, total_size));
	write(main_header_str());
    }

    public String jump(String label) {
	return "jmp " + label + "\n";
    }

    public String newLabel() {
	return "zn" + labelCounter++;
    }

    private String regId(int regNumber) {
	return regs[regNumber % n_regs];
    }

    public String dwordRegId(int regNumber) {
	return dwordRegs[regNumber % n_regs];
    }

    public String byteRegId(int regNumber) {
	return byteRegs[regNumber % n_regs];
    }

    public String intRegName(int regNumber){
	if (this.bits == 32){
	    return regId(regNumber);
	}
	else
	    return dwordRegId(regNumber);	    
    }

    public String realRegName(int regNumber){
	return regId(regNumber);
    }

    public String charRegName(int regNumber){
	return byteRegId(regNumber);
    }

    public String boolRegName(int regNumber){
	if (this.bits == 32){
	    return regId(regNumber);
	}
	else
	    return dwordRegId(regNumber);	    
    }

    public String addrRegName(int regNumber){
	    return regId(regNumber);
    }

    public String regName(int r, Type type) throws InvalidCodeException{
	if (type instanceof IntType)
	    return intRegName(r);
	else if (type instanceof FloatType)
	    return realRegName(r);
	else if (type instanceof BoolType)
	    return boolRegName(r);
	else if (type instanceof CharType)
	    return charRegName(r);
	else if ((type instanceof ListType)||
		 (type instanceof DictType)||
		 (type instanceof StringType))
	    return addrRegName(r);
	else
	    throw new InvalidCodeException("No se tienen registros para el tipo "+type);
    }

    public void write(String thing) throws IOException{
	file.write(thing);
    }

    public void writeLabel(String label) throws IOException {
	file.write(label + ":\n");
    }

    public void closeFile() throws IOException{
	file.close();
    }

    public String stack_pointer(){
	return this.stackp;
    }

    public String frame_pointer(){
	return this.framep;
    }

    public String global_offset(){
	return global_offset;
    }

    public String save(){
	String save;

	if (this.save != null){
	    save = this.save;
	    this.save = null;
	    return save;
	}
	else
	    return "";
    }

    public String restore(){
	String restore;

	if (this.restore != null){
	    restore = this.restore;
	    this.restore = null;
	    return restore;
	}
	else
	    return "";
    }

    public String get_reg(int reg){
	return regs[reg%n_regs];
    }

    //Suma 1 a next_reg y devuelve el string correspondiente.
    public String next_reg() {
	this.next_reg += 1;	

	//Seteo save y restore si es necesario
    	if (next_reg >= n_regs){
	    this.save = pushw(get_reg(next_reg));
	    this.restore = pop(get_reg(next_reg));
	}

	return regs[next_reg%n_regs];
    }

    //Resta a next_reg.
    public void prevs_regs(int n) {
	String exception = "";
	this.next_reg -= n;
	exception = regs[next_reg];
    }

    //Reserva tanta memoria como le pidan. data_size es la cantidad
    //de bytes. 
    public String reserve_space_str(String label, int data_size){
	return "section .bss\n   "+label+": resb "+data_size+"\n";
    }

    public String main_header_str(){
	return "section .text\n   global main\nmain:\n";
    }

    //Push
    public String push (String thing){
	String code = "";

	if (this.bits == 32)
	    return "push "+thing+"\n";
	else{
	    code += mov("[rsp]",thing);
	    code += sub("rsp",stackAlig);
	    return code;
	}
    }

    //Push de 32 bits (word)
    public String pushw (String thing){
	String code = "";

	if (this.bits == 32)
	    return "push "+thing+"\n";
	else{
	    code += mov("[rsp]",thing);
	    code += sub("rsp",Integer.toString(Integer.parseInt(stackAlig)/2));
	    return code;
	}
    }

    //Push de 64 bits (quad-word)
    public String pushq (String thing) throws InvalidCodeException{
	String code = "";
	if (this.bits == 64){
	    code += mov("[rsp]",thing);
	    code += sub("rsp",stackAlig);
	    return code;
	}
	else{
	    throw new InvalidCodeException("pushq en 32 bits");
	}
    }

    // Pop, la cantidad de bits es la misma
    //que la del destino (thing). Si nasm no
    //puede deducir la cantidad de bits,
    //va a dar error. En ese caso usar el otro pop.
    //(Esta funcion esta sobrecargada)
    public String pop (String thing){
	String code = "";

	if (this.bits == 32)
	    return "pop "+thing+"\n";
	else{
	    code += add("rsp",this.stackAlig);
	    code += mov(thing,"[rsp]");
	    return code;
	}
    }

    // Pop que especifica la cantidad de bits
    //que se deben mover. Si los bits son vacios
    //nasm deduce cuantos se deben mover, si puede.
    // Independiente de la arquitectura
    public String pop (String thing, String bits){
	String code = "";
	code += add(this.stackp,this.stackAlig);
	code += mov(thing,this.stackp,bits);
	return code;
    }

    public String pushInt (String in){
	if (this.bits == 32)
	    return push(in);
	else
	    return pushw(in);
    }

    public String pushReal (String real) throws InvalidCodeException{
	if (this.bits == 32)
	    return pushFloat(real);
	else
	    return pushDouble(real);
    }

    public String pushFloat (String flo){
	if (this.bits == 32)
	    return push(flo);
	else
	    return pushw(flo);
    }

    public String pushDouble (String dou) throws InvalidCodeException{
	if (this.bits == 64)
	    return push(dou);
	else{
	    throw new InvalidCodeException("pushDouble en 32 bits");
	}
    }

    public String pushChar (String ch){
	if (this.bits == 32)
	    return push(ch)+mov("["+this.stackp+"-4]","0h","byte");
	else
	    return pushw(ch)+mov("["+this.stackp+"-4]","0h","byte");
    }

    public String pushAddr (String addr){
	return push(addr);
    }

    // Usando este mov, nasm deducira la cantidad de
    //bytes a mover a partir del contexto.
    public String mov(String dst, String orig){
	return "mov "+dst+","+orig+"\n";
    }

    // Usando este mov, se le especifica explicitamente
    //a nasm la cantidad de bytes (byte,word,dword o qword).
    private String mov(String dst, String orig, String size_mod){
	return "mov "+size_mod+" "+dst+","+orig+"\n";
    }

    public String movInt(String dst, String orig){
	if (this.bits == 32)
	    return mov(dst,orig,"dword");
	else
	    return mov(dst,orig,"dword");	    
    }

    public String movReal(String dst, String orig){
	if (this.bits == 32)
	    return mov(dst,orig,"dword");
	else
	    return mov(dst,orig,"qword");	    
    }

    public String movBool(String dst, String orig){
	return mov(dst,orig,"dword");
    }

    public String movChar(String dst, String orig){
	return mov(dst,orig,"byte");
    }

    public String movAddr(String dst, String orig){
	if (this.bits == 32)
	    return mov(dst,orig,"dword");
	else
	    return mov(dst,orig,"qword");
    }

    public String fst(String dst, String size){
	return "fst "+size+" "+dst+"\n";
    }

    public String fstp(String dst, String size){
	return "fstp "+size+" "+dst+"\n";
    }

    public String fld(String orig, String size){
	return "fld "+size+" "+orig+"\n";
    }

    public String fst(String dst){
	return "fst "+dst+"\n";
    }

    public String fstp(String dst){
	return "fstp "+dst+"\n";
    }

    public String fld(String orig){
	return "fld "+orig+"\n";
    }

    public String fxch(){
	return "fxch\n";
    }

    public String fxchR(String st){
	return "fxch "+st+"\n";
    }

    public String ffree(String st){
	return "ffree "+st+"\n";
    }

    public String fninit(){
	return "fninit\n";
    }

    //Suma de enteros
    public String add(String dst, String op2){
	return "add "+dst+","+op2+"\n";
    }

    //Resta de enteros
    public String sub(String dst, String op2){
	return "sub "+dst+","+op2+"\n";
    }
    
    //Multiplicacion de enteros
    public String imul(String dst, String op2){
	return "imul "+dst+","+op2+"\n";
    }

    //Division de enteros, el resultado queda en dividend
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
	    code += mov(dividend,"eax");
	    code += pop("eax");
	}
	return code;
    }

    //Modulo de enteros, el resultado queda en dividend
    public String imod(String dividend, String diviser){
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
	if (dividend.compareTo("edx") == 0)
	    code += add(this.stackp,this.stackAlig);
	else{
	    code += mov(dividend,"edx");
	    code += pop("edx");
	}
	return code;
    }

    //Suma de flotantes
    //Para que esto funcione dst y op2 deben ser registros
    public String fadd(String dst, String op2){
	String code = "";
	String size;
	
	if (this.bits == 32)
	    size = "dword";
	else
	    size = "dword";
	
	code += mov("["+this.stackp+"]",dst);
	code += fld("["+this.stackp+"]",size);
	code += mov("["+this.stackp+"]",op2);
	code += fld("["+this.stackp+"]",size);
	code += "fadd st0,st1\n";
	code += fstp("["+this.stackp+"]",size);
	code += mov(dst,"["+this.stackp+"]");
	code += fninit();
	
	return code;
    }

    //Resta de flotantes
    public String fsub(String dst, String op2){
	String code = "";
	String size;
	
	if (this.bits == 32)
	    size = "dword";
	else
	    size = "dword";
	
	code += mov("["+this.stackp+"]",dst);
	code += fld("["+this.stackp+"]",size);
	code += mov("["+this.stackp+"]",op2);
	code += fld("["+this.stackp+"]",size);
	code += "fsub st0,st1\n";
	code += fstp("["+this.stackp+"]",size);
	code += mov(dst,"["+this.stackp+"]");
	code += fninit();
	
	return code;
    }
    
    //Multiplicacion de flotantes
    public String fmul(String dst, String op2){
	String code = "";
	String size;
	
	if (this.bits == 32)
	    size = "dword";
	else
	    size = "dword";
	
	code += mov("["+this.stackp+"]",dst);
	code += fld("["+this.stackp+"]",size);
	code += mov("["+this.stackp+"]",op2);
	code += fld("["+this.stackp+"]",size);
	code += "fmul st0,st1\n";
	code += fstp("["+this.stackp+"]",size);
	code += mov(dst,"["+this.stackp+"]");
	code += fninit();
	
	return code;
    }

    //Multiplicacion de flotantes
    public String fdiv(String dst, String op2){
	String code = "";
	String size;
	
	if (this.bits == 32)
	    size = "dword";
	else
	    size = "dword";
	
	code += mov("["+this.stackp+"]",dst);
	code += fld("["+this.stackp+"]",size);
	code += mov("["+this.stackp+"]",op2);
	code += fld("["+this.stackp+"]",size);
	code += "fdiv st0,st1\n";
	code += fstp("["+this.stackp+"]",size);
	code += mov(dst,"["+this.stackp+"]");
	code += fninit();
	
	return code;
    }

    public String and(String a, String b){
	return "and "+a+","+b+"\n";
    }

    public String or(String a, String b){
	return "or "+a+","+b+"\n";
    }

    public String xor(String a, String b){
	return "xor "+a+","+b+"\n";
    }

    public String cmp(String a, String b){
	return "cmp "+a+","+b+"\n";
    }

    public String jz(String label){
	return "jz "+label+"\n";
    }

    public String jnz(String label){
	return "jnz "+label+"\n";
    }

    public String je(String label){
	return "je "+label+"\n";
    }

    public String jne(String label){
	return "je "+label+"\n";
    }

    public String jg(String label){
	return "jg "+label+"\n";
    }

    public String jge(String label){
	return "jge "+label+"\n";
    }

    public String jl(String label){
	return "jl "+label+"\n";
    }

    public String jle(String label){
	return "jle "+label+"\n";
    }

    public String save_print_regs() throws InvalidCodeException{
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
	    code += pop("edx");
	    code += pop("ecx");
	    code += pop("ebx");
	    code += pop("eax");
	}
	else{
	    code += pop("r11");
	    code += pop("rcx");
	    code += pop("rdx");
	    code += pop("rsi");
	    code += pop("rdi");
	    code += pop("rax");
	}
	return code;
    }

    //El addr, si es un label, debe venir sin corchetes
    public String setup_print(String addr, String desc, String bytes){
	String code = "";

	if (this.bits == 32){
	    code += mov("eax","4"); //Codigo de sys_write 32 bits
	    code += mov("ebx",desc); //Descriptor a donde escribir (1=stdout)
	    code += mov("ecx",addr); //Direccion donde comienza el valor a imprimir
	    code += mov("edx",bytes); //Cantidad de bytes que se van a imprimir
	}
	else{
	    code += mov("rax","1"); //Codigo de sys_write 64 bits
	    code += mov("rdi",desc); //Descriptor a donde escribir (1=stdout)
	    code += mov("rsi",addr); //Direccion donde comienza el valor a imprimir
	    code += mov("rdx",bytes); //Cantidad de bytes que se van a imprimir
	}
	return code;
    }

    public void exitSyscall(int exit_code) throws IOException {
	String code = "\n";
	String e_code = Integer.toString(exit_code);

	if (this.bits == 64){
	    code += mov("rax","60");
	    code += mov("rdi",e_code);
	}
	else{
	    code += mov("eax","1");
	    code += mov("ebx",e_code);
	}
	code += syscall();

	write(code);
    }

    public String syscall(){
	if (this.bits == 32)
	    return "int 80h\n";
	else
	    return "syscall\n";
    }

    public String toASCII(char C){
	return DataTranslator.toASCII(C);
    }

    public String toReal(double F){
	if (bits == 32)
	    return DataTranslator.toReal((float)F);
	else
	    return DataTranslator.toReal(F);
    }

    public String toReal(float F){
	return DataTranslator.toReal(F);
    }
}