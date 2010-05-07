package zinara.ast.expression;
import zinara.code_generator.*;

import zinara.ast.type.Type;
import zinara.exceptions.TypeClashException;
import zinara.parser.sym;
import zinara.parser.parser;

import java.io.IOException;

public class BinaryExp extends Expression {
    public int operator;
    public Expression left;
    public Expression right;
    
    public BinaryExp (int o, Expression l, Expression r) {
	operator=o;
	left=l;
	right=r;
    }
    
    public Type getType() throws TypeClashException {
	return parser.operators.check(this.operator, this.left.getType(), this.right.getType());
    }

    public String toString() {
	return "("+left + " " + operator + " " + right+")" ;
    }

    public String tox86(Genx86 generate) throws IOException{
	String code = "";
	int regs_used = 1;
	
	String exp1Reg = generate.current_reg();
	String exp2Reg;
	
	code += left.tox86(generate);

	exp2Reg = generate.next_reg();
	code += right.tox86(generate);

	if (operator == sym.PLUS){
	    code += generate.add(exp1Reg,exp2Reg);
	}
	else if (operator == sym.MINUS){
	    code += generate.sub(exp1Reg,exp2Reg);
	}
	else if (operator == sym.TIMES){
	    code += generate.imul(exp1Reg,exp2Reg);
	}
	else if (operator == sym.DIVIDE){
	    code += generate.idiv(exp1Reg,exp2Reg);
	}
	else{
	    System.out.println("Operacion no implementada: "+operator);
	    System.exit(1);
	}

	generate.prevs_regs(regs_used);
        return code;
    }
}
