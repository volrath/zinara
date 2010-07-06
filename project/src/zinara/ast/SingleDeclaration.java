package zinara.ast;

import java.io.IOException;

import zinara.ast.ASTNode;
import zinara.ast.Param;
import zinara.ast.type.Type;
import zinara.ast.expression.Expression;
import zinara.ast.expression.BooleanExp;
import zinara.ast.expression.Identifier;
import zinara.ast.type.*;
import zinara.code_generator.Genx86;
import zinara.exceptions.TypeClashException;
import zinara.exceptions.InvalidCodeException;
import zinara.symtable.*;

public class SingleDeclaration extends Declaration {
    private Type type;
    private String identifier;
    private Status status;
    private Expression expr;
    private SymTable symTable;
    
    public SingleDeclaration(Type t, String id, Expression expr, boolean var, SymTable st) throws TypeClashException {
	// Type checking first
	if (expr != null && !t.equals(expr.getType()))
	    throw new TypeClashException("Asignacion invalida: tipo de la expresion `" + expr + "`" + expr.getType() + " difiere del tipo " + t + " en la declaracion del identificador " + id);
	// ...
	this.type = t;
	this.identifier = id;
	this.expr = expr;
	this.symTable = st;
	if (var)
	    status = new Variable(); else status = new Constant(expr);
    }

    public SingleDeclaration(Type t, Identifier id, Expression expr, boolean var, SymTable st) throws TypeClashException {
	// Type checking first
	if (expr != null && !t.equals(expr.getType()))
	    throw new TypeClashException("Asignacion invalida: tipo de la expresion `" + expr + "`" + expr.getType() + " difiere del tipo " + t + " en la declaracion del identificador " + id.getIdentifier());
	// ...
	this.type = t;
	this.identifier = id.getIdentifier();
	this.expr = expr;
	this.symTable = st;
	if (var) status = new Variable(); else status = new Constant(expr);
    }

    public boolean isSingle(){
	return true;
    }

    public Type getType(){
	return this.type;
    }

    public String getId(){
	return this.identifier;
    }

    public Expression getExpression() { return expr; }

    public Status getStatus() { return status; }

    public void setType(Type t) { this.type = t; }

    public String toString() {
	return "(Declaration: " + type + " " + identifier + " [" + status + "])";
    }

    public void tox86(Genx86 generator)
	throws IOException, InvalidCodeException {

	if (this.type instanceof RoutineType){
	    String label = generator.newLabel();
	    label = label + "_" + identifier;
	    RoutineType routine_type = (RoutineType)(symTable.getSymbol(identifier).type);
	    int local_vars;

	    //Seteo el offset de las variables de la subrutina
	    SymTable routineTable = routine_type.codeBlock.getSymTable();
	    String frame_p = generator.frame_pointer();
	    int word_size = generator.word_size();

	    local_vars = routineTable.reserve_mem_stack(word_size,frame_p);
	    routineTable.set_params_offset(frame_p,
					   word_size,
					   routine_type.args);

	    //Set del label del procedimiento en el Symtable
	    ((RoutineType)(this.type)).label = label;
	    routine_type.label = label;

	    make_proc(generator,label,local_vars);

	    return;
	}

	
	if (expr != null) {
	    SymValue sv = symTable.getSymbol(identifier);
	    String exprReg;
	    String lvalueAddr = sv.getArea()+sv.getOffset();
	    
	    expr.register = register;
	    if (type.equals(new BoolType())) {
		booleanAssignationToX86(generator, lvalueAddr);
		return;
	    }

	    expr.tox86(generator);

	    exprReg = generator.regName(expr.register,expr.type);

	    storeValue(generator, type, lvalueAddr, exprReg);
	}
    }

    // This one can be improved =S
    public void booleanAssignationToX86(Genx86 generator, String lvalueAddr)
	throws IOException,InvalidCodeException,TypeClashException{
	BooleanExp bExpr = (BooleanExp)expr;
	String nextDecl = generator.newLabel();

	bExpr.yesLabel  = generator.newLabel();
	bExpr.noLabel   = generator.newLabel();

	//En caso de que bExpr necesite computarse
	bExpr.register = register;
	String bExprReg = generator.regName(bExpr.register,bExpr.type);

	bExpr.tox86(generator);
	if (!(bExpr instanceof BooleanExp)){
	    generator.add(bExprReg,"0");
	    generator.jz(bExpr.noLabel);
	}

	generator.writeLabel(bExpr.yesLabel);

	generator.write(generator.movBool("[" + lvalueAddr + "]", "1"));

	generator.write(generator.jump(nextDecl));

	generator.writeLabel(bExpr.noLabel);

	generator.write(generator.movBool("[" + lvalueAddr + "]", "0"));

	generator.writeLabel(nextDecl);
    }

    private void storeValue(Genx86 generator, Type t, String lvalueAddr, String exprReg)
	throws IOException,InvalidCodeException,TypeClashException{
	
	if (t.getType() instanceof ListType) {
	    Type listType = ((ListType)t.getType()).getInsideType();
	    String auxReg = generator.regName(register+1,listType);
	    String lvalueReg = generator.addrRegName(register+2);

	    generator.write(generator.save(register+1));
	    generator.write(generator.save(register+2));

	    generator.write(generator.mov(lvalueReg,lvalueAddr));
	    int j = 1;
	    for (int i = ((ListType)t.getType()).len(); i > 0; i--) {
		generator.write(generator.mov(auxReg,"["+exprReg+"]",listType));
		generator.write(generator.mov("["+lvalueReg+"]",auxReg,listType));

		generator.write(generator.add(lvalueReg,Integer.toString(listType.size())));
		generator.write(generator.add(exprReg,Integer.toString(listType.size())));
	    }

	    generator.write(generator.restore(register+2));
	    generator.write(generator.restore(register+1));
	}
	else{
	    generator.write(generator.mov("[" + lvalueAddr + "]",
					  exprReg, t.getType()));
	}
    }

    private void make_proc(Genx86 generator,String label,int local_vars)
	throws InvalidCodeException,IOException,TypeClashException{
	String asm = "";
	String local_vars_size = Integer.toString(local_vars);
	String frame_p = generator.frame_pointer();
	String stack_p = generator.stack_pointer();
	String word_size = Integer.toString(generator.word_size());
	
	asm += label+":\n";

	//Guardo la cadena dinamica
	asm += generator.pushAddr(frame_p);

	//Actualizo el frame pointer
	asm += generator.mov(frame_p,stack_p);

	//Variables locales
	asm += generator.sub(stack_p,local_vars_size);

	//Registros salvados
	asm += generator.save_regs_callee();

	generator.write(asm);

	((RoutineType)type).codeBlock.register = 0;
	((RoutineType)type).codeBlock.tox86(generator);

	asm = "";
	asm += generator.restore_regs_callee();

	//Se desempila todo que esta despues de la cadena dinamica
	asm += generator.mov(stack_p,frame_p);

	//Se restaura la cadena dinamica
	asm += generator.pop(frame_p);
	
	//Return
	asm += generator.ret();
	generator.write(asm);
    }
}
