package zinara.semantic;

import java.util.ArrayList;

import zinara.ast.expression.Expression;
import zinara.ast.expression.CallExp;
import zinara.ast.instructions.Return;
import zinara.ast.instructions.CallInst;
import zinara.ast.type.Type;
import zinara.ast.type.ListType;
import zinara.ast.type.FunctionType;
import zinara.exceptions.IdentifierNotDeclaredException;
import zinara.exceptions.InvalidInstructionException;
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
    //@ requires expr != null;
    //@ requires type != null;
//     public static void checkExpressionSoft(Expression expr, Type type)
// 	throws TypeClashException {
// 	if (!( expr.getType() instanceof typeClass ))
// 	    throw new TypeClashException("Conflicto de tipos en la expresion " + expr + ". Se espera " + type + " y se obtuvo " + expr.getType());
//     }

    /*
      Checks if a given expression is instance of a given type
     */
    //@ requires expr != null;
    //@ requires type != null;
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
	SymValue idSymValue = st.getSymbolRecursively("return");
	if (idSymValue != null) { // we're inside a funtion
	    if (expr.getType().equals(idSymValue.getType())) return new Return(expr);
	    else throw new TypeClashException("Tipo de retorno de la funcion " + idSymValue.getType() + " difiere del tipo de la expresion " + expr);
	} else throw new InvalidInstructionException("Instruccion `return` no permitida en el main");
    }

    public static CallExp checkCallExp(String funcName, ArrayList expr_list, SymTable st)
	throws TypeClashException, IdentifierNotDeclaredException {
	SymValue idSymValue = st.getSymbolOrDie(funcName);
	if (!idSymValue.getType().equals(new FunctionType(null, null, null))) throw new TypeClashException("El identificador " + funcName + " tiene tipo " + idSymValue.getType() + ", no es una funcion");
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
	SymValue idSymValue = st.getSymbolOrDie(funcName);
	if (!idSymValue.getType().equals(new FunctionType(null, null, null))) throw new TypeClashException("El identificador " + funcName + " tiene tipo " + idSymValue.getType() + ", no es una funcion");
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
}
