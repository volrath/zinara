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
    private String stackAlig; //Alineamiento de la pila
    private String data_offset;
    
    private int n_regs;
    private int next_reg;
    private int bits;

    private BufferedWriter file;

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
	
	this.data_offset = "glob";

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

    //Devuelve el registro actual
    public String current_reg(){
	return this.regs[next_reg%n_regs];
    }

    public String stack_pointer(){
	return this.stackp;
    }

    public String frame_pointer(){
	return this.framep;
    }

    public String data_offset(){
	return this.data_offset;
    }

    public String get_reg(int reg){
	return regs[reg%n_regs];
    }

    //Suma 1 a next_reg y devuelve el string correspondiente.
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

    //Resta a next_reg.
    public void prevs_regs(int n) {
	String exception = "";
	this.next_reg -= n;
	exception = regs[next_reg];
    }

    //Reserva tanta memoria como le pidan. data_size es la cantidad
    //de bytes. 
    public String data(String label, int data_size){
	return "section .bss\n   "+label+": resb "+data_size+"\n";
    }

    public String main_text_header(){
	return "section .text\n   global _start\n   _start:\n";
    }

    //Push de 32 bits (word)
    public String pushw (String thing){
	String code = "";

	if (this.bits == 32)
	    return "push "+thing+"\n";
	else{
	    code += mov("[rsp]",thing);
	    code += mov("[rsp+4]","0h","dword");
	    code += sub("rsp",stackAlig);
	    return code;
	}
    }

    //Push de 64 bits (quad-word)
    public String pushq (String thing){
	String code = "";
	if (this.bits == 64){
	    code += mov("[rsp]",thing);
	    code += sub("rsp",stackAlig);
	    return code;
	}
	else{
	    System.out.println("pushq en 32 bits");
	    System.exit(1);
	}
	return "";
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

    // Usando este mov, nasm deducira la cantidad de
    //bytes a mover a partir del contexto.
    public String mov(String dst, String orig){
	return "mov "+dst+","+orig+"\n";
    }

    // Usando este mov, se le especifica explicitamente
    //a nasm la cantidad de bytes (byte,word,dword o qword).
    public String mov(String dst, String orig, String size_mod){
	return "mov "+size_mod+" "+dst+","+orig+"\n";
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

    public String exit_syscall(int exit_code){
	String code = "";
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

	return code;
    }

    public String syscall(){
	if (this.bits == 32)
	    return "int 80h\n";
	else
	    return "syscall\n";
    }
}