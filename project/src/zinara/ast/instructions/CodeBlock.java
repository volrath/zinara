package zinara.ast.instructions;
import zinara.code_generator.*;

import java.io.IOException;
import java.util.ArrayList;

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

    public String toString() {
	String ret = "<CodeBlock:";
	for (int i = 0; i < block.size(); i++)
	    ret += " " + (Instruction)block.get(i) + ",";
	return (ret.substring(0, ret.length()-1) + ">");
    }

    public String tox86(Genx86 generate) throws IOException{
	for (int i = 0; i < block.size(); i++)
	    ((Instruction)block.get(i)).tox86(generate);

        return "";
    }
}
