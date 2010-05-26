package zinara.ast.expression;

import zinara.ast.type.*;
import zinara.code_generator.*;
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
	if (type != null) return type;
	type = parser.operators.check(this.operator, this.left.getType(), this.right.getType());
	return type;
    }

    public String toString() {
	return "("+left + " " + operator + " " + right+")" ;
    }

    public void tox86(Genx86 generate) throws IOException {
	int regs_used = 1;
	Type type = this.type;
	
	String save;
	String restore;

	String exp1Reg = generate.current_reg();
	String exp2Reg;
	
	left.tox86(generate);
	generate.write(generate.save());
	exp2Reg = generate.next_reg();
	right.tox86(generate);

	if (type instanceof IntType)
	    generate.write(intOps(generate,exp1Reg,exp2Reg));
	else if (type instanceof FloatType)
	    generate.write(realOps(generate,exp1Reg,exp2Reg));
	else{
	    System.out.println("Tipo no implementado: "+operator);
	    System.exit(1);
	}

	generate.prevs_regs(regs_used);

	generate.write(generate.restore());
        //generate.write(code);
    }

    private String intOps(Genx86 generate, String exp1Reg, String exp2Reg){
	String code = "";

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
	else if (operator == sym.MOD){
	    code += generate.imod(exp1Reg,exp2Reg);
	}
	else{
	    System.out.println("Operacion no implementada para enteros: "+operator);
	    System.exit(1);
	}
	
	return code;
    }

    private String realOps(Genx86 generate, String exp1Reg, String exp2Reg){
	String code = "";

	if (operator == sym.PLUS){
	    code += generate.fadd(exp1Reg,exp2Reg);
	}
	else if (operator == sym.MINUS){
	    code += generate.fsub(exp1Reg,exp2Reg);
	}
	else if (operator == sym.TIMES){
	    code += generate.fmul(exp1Reg,exp2Reg);
	}
	else if (operator == sym.DIVIDE){
	    code += generate.fdiv(exp1Reg,exp2Reg);
	}
	else{
	    System.out.println("Operacion no implementada para reales: "+operator);
	    System.exit(1);
	}
	
	return code;
    }
}
