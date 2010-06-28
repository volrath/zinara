package zinara.ast.instructions;

import java.io.IOException;
import java.util.ArrayList;

import zinara.ast.instructions.DecInst;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;
import zinara.symtable.SymTable;

public class CodeBlock extends Instruction{
    private ArrayList block;   // ArrayList of Instructions
    private SymTable symTable;

    public CodeBlock() { this.block = new ArrayList(); }

    public CodeBlock(ArrayList b){
	this.block = b;
    }

    public ArrayList getBlock(){
	return this.block;
    }

    public void addInst(Instruction i){
	this.block.add(i);
    }

    public void setSymTable(SymTable st) { this.symTable = st; }

    public SymTable getSymTable() { return this.symTable; }

    public String toString() {
	String ret = "<CodeBlock:";
	for (int i = 0; i < block.size(); i++)
	    ret += " " + (Instruction)block.get(i) + ",";
	return (ret.substring(0, ret.length()-1) + ">");
    }

    public void checkNoReturns(){
	Instruction ins;
	for(int i = 0; i<block.size(); i++){
	    ins=((Instruction)block.get(i));
	    if (ins instanceof Return){
		System.out.println("return fuera de una funcion");
		System.exit(1);
	    }
	    else
		ins.checkNoReturns();
	}
    }

    public void tox86(Genx86 generator)
	throws IOException,InvalidCodeException,TypeClashException{
	Instruction inst;
	
	for (int i = 0; i < block.size(); i++) {
	    inst = (Instruction)block.get(i);
	    //if (inst instanceof DecInst) continue; // this really doesnt belong here

	    inst.register = register;
	    inst.nextInst = ((i != block.size() - 1) ? generator.newLabel() : nextInst);
	    System.out.println("writing " + inst + " -> " + inst.nextInst);
	    inst.tox86(generator);
	    if (i != block.size() - 1) generator.writeLabel(inst.nextInst);
	}
    }
}
