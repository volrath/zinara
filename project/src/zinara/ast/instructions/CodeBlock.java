package zinara.ast.instructions;

import java.util.ArrayList;

public class CodeBlock extends Instruction{
    private ArrayList block;   // ArrayList of... ?

    public CodeBlock(ArrayList b){
	this.block = b;
    }

    public ArrayList getBlock(){
	return this.block;
    }

    public void addInst(Instruction i){
	this.block.add(i);
    }
}
