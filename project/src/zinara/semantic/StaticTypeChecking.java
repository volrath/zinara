package zinara.semantic;

import java.util.ArrayList;

import zinara.ast.expression.Expression;
import zinara.ast.expression.IntegerExp;
import zinara.ast.expression.LValue;
import zinara.ast.expression.LValueList;
import zinara.ast.expression.LValueTuple;
import zinara.ast.expression.LValueDict;
import zinara.ast.expression.Identifier;
import zinara.ast.expression.CallExp;
import zinara.ast.instructions.Return;
import zinara.ast.instructions.CallInst;
import zinara.ast.type.Type;
import zinara.ast.type.DictType;
import zinara.ast.type.IntType;
import zinara.ast.type.ListType;
import zinara.ast.type.TupleType;
import zinara.ast.type.FunctionType;
import zinara.exceptions.IdentifierNotDeclaredException;
import zinara.exceptions.InvalidAccessException;
import zinara.exceptions.InvalidInstructionException;
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
	if (!(expr.getType() instanceof ListType))
	    throw new TypeClashException("La expresion " + expr + " no es iterable.");
    }

    /*
      Checks two things:
      1. the return statement is inside of a function. If it's not
      then throw an InvalidInstructionException
      2. the expression after the return statement is the same type of
      the defined function
     */
    //@ requires expr != null;
    //@ requires st != null;
    public static Return checkReturnValue(Expression expr, SymTable st)
	throws TypeClashException, InvalidInstructionException {
	SymValue idSymValue = st.getSymValueForId("return");
	if (idSymValue != null) { // we're inside a funtion
	    if (expr.getType().equals(idSymValue.getType())) return new Return(expr);
	    else throw new TypeClashException("Tipo de retorno de la funcion " + idSymValue.getType() + " difiere del tipo de la expresion " + expr);
	} else throw new InvalidInstructionException("Instruccion `return` no permitida en el main");
    }

    public static CallExp checkCallExp(String funcName, ArrayList expr_list, SymTable st)
	throws TypeClashException, IdentifierNotDeclaredException {
	SymValue idSymValue = st.getSymValueForIdOrDie(funcName);
	if (!(idSymValue.getType() instanceof FunctionType)) throw new TypeClashException("El identificador " + funcName + " tiene tipo " + idSymValue.getType() + ", no es una funcion");
	FunctionType funcType = (FunctionType)idSymValue.getType();

	// Check every argument
	Expression currentExpr;
	for (int i = 0; i < expr_list.size(); i++) {
	    currentExpr = (Expression)expr_list.get(i);
	    if (!currentExpr.getType().equals(funcType.getArgument(i)))
		throw new TypeClashException("El tipo de la expresion " + currentExpr + " difiere del tipo del argumento " + (i+1) + " de la funcion " + funcName);
	}
	return new CallExp(funcName, expr_list);
    }

    public static CallInst checkCallInst(String funcName, ArrayList expr_list, SymTable st)
	throws TypeClashException, IdentifierNotDeclaredException {
	SymValue idSymValue = st.getSymValueForIdOrDie(funcName);
	if (!(idSymValue.getType() instanceof FunctionType)) throw new TypeClashException("El identificador " + funcName + " tiene tipo " + idSymValue.getType() + ", no es una funcion");
	FunctionType funcType = (FunctionType)idSymValue.getType();

	// Check every argument
	Expression currentExpr;
	for (int i = 0; i < expr_list.size(); i++) {
	    currentExpr = (Expression)expr_list.get(i);
	    if (!currentExpr.getType().equals(funcType.getArgument(i)))
		throw new TypeClashException("El tipo de la expresion " + currentExpr + " difiere del tipo del argumento " + (i+1) + " de la funcion " + funcName);
	}
	return new CallInst(funcName, expr_list);
    }

    /*
      Checks if some lvalue is well-constructed, this work only for
      Lists or Tuples, the Dictionary checking is on the next static
      method.
     */
    public static LValue checkAndReturnLValue(LValue lv, Expression expr)
	throws InvalidAccessException, TypeClashException, KeyErrorException {
	Type lvType = lv.getType();
	ListType emptyList = new ListType();
	TupleType emptyTuple = new TupleType();
	if (!(lvType.equals(emptyList)) && !(lvType.equals(emptyTuple)))
	    throw new InvalidAccessException("La expresion " + lv + " no es del tipo lista o tupla y no puede ser indexada con una expresion. ");
	if (lvType.equals(emptyList))
	    if (!(expr.getType() instanceof IntType))
		throw new InvalidAccessException("La expresion " + lv + " es del tipo " + lvType + " y la expresion " + expr + " debe ser del tipo Int para poder realizar el indexamiento");
	    else
		return new LValueList(lv, expr);
	if (lvType.equals(emptyTuple))
	    if (!(expr instanceof IntegerExp))
		throw new InvalidAccessException("La expresion " + lv + " es del tipo Tuple y debe ser indexada unicamente por enteros literales");
	    else
		return new LValueTuple(lv, ((IntegerExp)expr).getValue());
	throw new InvalidAccessException("Diccionarios todavia no estan implementados");
    }

    //@requires lv != null;
    //@requires id != null;
    //@requires ct != null;
    public static LValue checkAndReturnLValue(LValue lv, String id, SymTable ct) 
	throws InvalidAccessException, TypeClashException, KeyErrorException, IdentifierNotDeclaredException {
	Type lvType = lv.getType();
	//@assume lv.getType() != null;
	if (lvType instanceof ListType) {
	    SymTable st = ct.getSymTableForId(id);
	    if (st == null) throw new IdentifierNotDeclaredException(id);
	    SymValue sv = st.getSymValueForId(id);
	    //@assume sv != null;
	    if (sv.getType() instanceof IntType)
		return new LValueList(lv, new Identifier(id, st));
	    else
		throw new InvalidAccessException("El identificador " + id + " tiene tipo " + sv.getType() + ", se requiere Int");
	}
	if (!(lvType instanceof DictType))
	    throw new InvalidAccessException("La expresion " + lv + " no representa un diccionario y no puede ser indexado con un identificador.");
	return new LValueDict(lv, id);
    }
}

