package zinara.semantic;

import java.util.ArrayList;

import zinara.ast.expression.Expression;
import zinara.ast.expression.BooleanExp;
import zinara.ast.expression.IntegerExp;
import zinara.ast.expression.LValue;
import zinara.ast.expression.LValueList;
import zinara.ast.expression.LValueTuple;
import zinara.ast.expression.LValueDict;
import zinara.ast.expression.LValueVariant;
import zinara.ast.expression.Identifier;
import zinara.ast.expression.FunctionCall;
import zinara.ast.instructions.CodeBlock;
import zinara.ast.instructions.Instruction;
import zinara.ast.instructions.Return;
import zinara.ast.instructions.ProcedureCall;
import zinara.ast.instructions.SetVariant;
import zinara.ast.type.Type;
import zinara.ast.type.DictType;
import zinara.ast.type.IntType;
import zinara.ast.type.ListType;
import zinara.ast.type.TupleType;
import zinara.ast.type.FunctionType;
import zinara.ast.type.ProcedureType;
import zinara.ast.type.VariantType;
import zinara.exceptions.IdentifierNotDeclaredException;
import zinara.exceptions.InvalidAccessException;
import zinara.exceptions.InvalidInstructionException;
import zinara.exceptions.InvalidVariantException;
import zinara.exceptions.KeyErrorException;
import zinara.exceptions.TypeClashException;
import zinara.symtable.*;

public class StaticTypeChecking {
    public static boolean compareTypes(Type type1, Type type2) {
	return (type1 == type2);
    }

    /*
      Checks if a given expression is of a given type
     */
    //@ requires expr != null;
    //@ requires type != null;
    public static void checkExpression(Expression expr, Type type)
	throws TypeClashException {
	if (!type.equals(expr.getType()))
	    throw new TypeClashException("Conflicto de tipos en la expresion " + expr + ". Se espera " + type + " y se obtuvo " + expr.getType());
    }

    /*
      Checks if a given expression is instance of a given type
     */
    // requires expr != null;
    // requires type != null;
//     public static void checkExpressionSoft(Expression expr, Type type)
// 	throws TypeClashException {
// 	if (!( expr.getType() instanceof typeClass ))
// 	    throw new TypeClashException("Conflicto de tipos en la expresion " + expr + ". Se espera " + type + " y se obtuvo " + expr.getType());
//     }

    /*
      Checks if a given expression is instance of a given type
     */
    //@ requires expr != null;
    public static void checkIterable(Expression expr)
	throws TypeClashException {
	if (!(expr.getType().getType() instanceof ListType))
	    throw new TypeClashException("La expresion " + expr + expr.getType() + " no es iterable.");
    }

    /*
      Checks two things:
      1. the return statement only can be inside of a function. If
      it's not then throw an InvalidInstructionException
      2. the expression after the return statement is the same type of
      the defined function
     */
    //@ requires expr != null;
    //@ requires st != null;
    public static Return checkReturnValue(Expression expr, SymTable st)
	throws TypeClashException, InvalidInstructionException {
	SymValue idSymValue = st.getSymValueForId("return");
	if (idSymValue != null) { // we're inside a funtion
	    if (idSymValue.getType() == null)
		throw new InvalidInstructionException("Instruccion `return` no permitida en un procedimiento");
	    else if (expr.getType().equals(idSymValue.getType()))
		return new Return(expr);
	    else 
		throw new TypeClashException("Tipo de retorno de la funcion " + 
					     idSymValue.getType() + 
					     " difiere del tipo de la expresion " + 
					     expr);
	}
	else 
	    throw new InvalidInstructionException("Instruccion `return` no permitida en el main");
    }

    /*
      The return statement has to be at least once inside the codeblock
     */
    public static void checkReturnStatement(String funcName, CodeBlock code) throws InvalidInstructionException {
	boolean found = false;
	Instruction inst;
	for (int i = 0; i < code.getBlock().size(); i++) {
	    inst = (Instruction)code.getBlock().get(i);
	    found = found || (inst instanceof Return);
	}
	if (!found)
	    throw new InvalidInstructionException("La función " + funcName + " no tiene return");
    }

    public static FunctionCall checkFunctionCall(String funcName, ArrayList expr_list, SymTable st)
	throws TypeClashException, IdentifierNotDeclaredException, InvalidAccessException {
	SymValue idSymValue = st.getSymValueForIdOrDie(funcName);
	if (!(idSymValue.getType() instanceof FunctionType))
	    throw new TypeClashException("El identificador " + 
					 funcName +
					 " tiene tipo " +
					 idSymValue.getType() +
					 ", no es una funcion");
	FunctionType funcType = (FunctionType)idSymValue.getType();

	// Check every argument
	Expression currentExpr;
	for (int i = 0; i < expr_list.size(); i++) {
	    currentExpr = (Expression)expr_list.get(i);
	    if (!currentExpr.getType().equals(funcType.getArgumentType(i)))
		throw new TypeClashException("El tipo de la expresion " +
					     currentExpr +
					     " difiere del tipo del argumento " +
					     (i+1) +
					     " de la funcion " +
					     funcName);
	    if (funcType.isArgumentByRef(i) && !(currentExpr instanceof LValue))
		throw new InvalidAccessException("La expresion " + currentExpr + " no puede ser pasada como parametro por referencia");
	}
	return new FunctionCall(funcName, expr_list, st);
    }

    public static ProcedureCall checkProcedureCall(String procName, ArrayList expr_list, SymTable st)
	throws TypeClashException, IdentifierNotDeclaredException, InvalidAccessException {
	SymValue idSymValue = st.getSymValueForIdOrDie(procName);
	if (!(idSymValue.getType() instanceof ProcedureType))
	    throw new TypeClashException("El identificador " + procName + " no es un procedimiento");
	ProcedureType procType = (ProcedureType)idSymValue.getType();

	// Check every argument
	Expression currentExpr;
	for (int i = 0; i < expr_list.size(); i++) {
	    currentExpr = (Expression)expr_list.get(i);
	    if (!currentExpr.getType().equals(procType.getArgumentType(i)))
		throw new TypeClashException("El tipo de la expresion " + currentExpr + " difiere del tipo del argumento " + (i+1) + " de la funcion " + procName);
	    if (procType.isArgumentByRef(i) && !(currentExpr instanceof LValue))
		throw new InvalidAccessException("La expresion " + currentExpr + " no puede ser pasada como parametro por referencia");
	}
	return new ProcedureCall(procName, expr_list, st);
    }

    /*
      Checks if some lvalue is well-constructed, this work only for
      Lists or Tuples, the Dictionary checking is on the next static
      method.
     */
    public static LValue checkAndReturnLValue(LValue constructor, Expression expr)
	throws InvalidAccessException, TypeClashException, KeyErrorException {

	Type constructorType = constructor.getType().getType();

	if (!(constructorType instanceof TupleType) && !(constructorType instanceof ListType))
	    throw new InvalidAccessException("La expresion " + constructor + " no es del tipo lista o tupla y no puede ser indexada con una expresion. ");

	if (constructorType instanceof ListType)
	    if (!(expr.getType() instanceof IntType))
		throw new InvalidAccessException("La expresion " + expr + " es del tipo " + expr.getType() + " pero debe ser del tipo Int para poder realizar el indexamiento");
	    else
		return new LValueList(constructor, expr);

	if (constructorType instanceof TupleType)
	    if (!(expr.getType() instanceof IntType))
		throw new InvalidAccessException("La expresion " + expr + " es del tipo " + expr.getType() + " pero debe ser del tipo Int para poder realizar el indexamiento");
	    else if (!expr.isStaticallyKnown())
		throw new InvalidAccessException("La expresion " + expr + " debe ser un entero literal");
	    else {
		System.out.println("IS STATICALLY KNOWN " + expr + ":" + expr.staticValue());
		return new LValueTuple(constructor, ((Integer)expr.staticValue()).intValue());
	    }

	throw new InvalidAccessException("Diccionarios todavia no estan implementados");
    }

    //@requires constructor != null;
    //@requires id != null;
    //@requires ct != null;
    public static LValue checkAndReturnLValue(LValue constructor, String id, SymTable ct) 
	throws InvalidAccessException, TypeClashException, KeyErrorException, IdentifierNotDeclaredException {
	Type constructorType = constructor.getType().getType();
	//@assume constructor.getType() != null;
// 	if (constructorType instanceof ListType) {
// 	    SymTable st = ct.getSymTableForId(id);
// 	    if (st == null) throw new IdentifierNotDeclaredException(id);
// 	    SymValue sv = st.getSymValueForId(id);
// 	    //@assume sv != null;
// 	    if (sv.getType() instanceof IntType)
// 		return new LValueList(constructor, new Identifier(id, st));
// 	    else
// 		throw new InvalidAccessException("El identificador " + id + " tiene tipo " + sv.getType() + ", se requiere Int");
// 	}
	if (!(constructorType instanceof DictType) && !(constructorType instanceof VariantType))
	    throw new InvalidAccessException("La expresion " + constructor + " no representa un diccionario o una variante y no puede ser indexado con un identificador.");
	if (constructorType instanceof DictType)
	    return new LValueDict(constructor, id);
	else
	    return new LValueVariant(constructor, id);
    }

    public static int returnStaticInt(Expression expr) throws TypeClashException {
	// Checks if the expression is statically known, and if it is,
	// check if it's an integer..
	if (!(expr.getType() instanceof IntType))
	    throw new TypeClashException("La expresion es de tipo " + expr.getType() + " y es necesario que sea de tipo <INT> para ser tamano de una lista");
	if (!expr.isStaticallyKnown())
	    throw new TypeClashException("La expresion " + expr + " no puede ser calculada a tiempo de compilación");
	Object s = expr.staticValue();
	if (!(s instanceof Integer))
	    throw new TypeClashException("La expresion " + expr + " no pudo ser reducida a un entero");
	return ((Integer)s).intValue();
    }

    public static SetVariant checkVariantChange(LValue lv, String var)
	throws TypeClashException, InvalidVariantException {
	Type lvType = lv.getType().getType();
	if (!(lvType instanceof VariantType))
	    throw new InvalidVariantException("El identificador " + lv + " no es una variante");
	if (((VariantType)lvType).getVariant(var) == null)
	    throw new InvalidVariantException("El identificador " + lv + " no tiene una variante con nombre " + var);
	return new SetVariant(lv, var);
    }
}

