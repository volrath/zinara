package zinara.ast.instructions;

import java.util.ArrayList;

class CodeBlock extends Instruction{
    private ArrayList block;

    public CodeBlock(ArrayList b){
	this.block = b;
    }

    public ArrayList getBlock(){
	return this.block;
    }
}
