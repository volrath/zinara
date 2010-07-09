package zinara.ast;

import zinara.ast.Param;
import zinara.ast.RoutineGenerator;
import zinara.ast.expression.Expression;
import zinara.ast.expression.Identifier;
import zinara.ast.expression.ListExp;
import zinara.ast.type.Type;
import zinara.ast.type.FunctionType;
import zinara.ast.type.RoutineType;
import zinara.ast.type.ListType;
import zinara.ast.type.TupleType;
import zinara.ast.type.DictType;
import zinara.code_generator.*;
import zinara.exceptions.InvalidCodeException;
import zinara.symtable.*;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;

public class RoutineGenerator{

    public static void gen_routine(Genx86 generator,
				   SymTable symTable,
				   String func_name,
				   ArrayList expr_list,
				   int register,
				   boolean isFunction)
	throws InvalidCodeException,IOException{
	String code = "";

	SymValue proc = symTable.getSymValueForId(func_name);
	RoutineType routine = (RoutineType)(proc.type);
	
	Expression expr;
	Type exprType;

	String reg;
	String ax;

	int params_size = 0;

	code += generator.save_regs_caller(register);
	for (int i = 0; i < expr_list.size() ; i++){
	    expr = (Expression)expr_list.get(i);
	    expr.register = register;

	    //Caso por valor
	    if ( ((Param)routine.getArgument(i)).byValue() ){
		//Seteo el nombre correcto del registro a utilizar
		//exprType = expr.getType();
		exprType = expr.type;
		reg = generator.regName(register,exprType);
		
		/*********Se pushea en la pila*********/		
		//Si es un tipo basico lo pusheo
		if (!(exprType instanceof ListType)&&
		    !(exprType instanceof TupleType)&&
		    !(exprType instanceof DictType)){

		    //Se genera el valor
		    expr.tox86(generator);

		    reg = generator.regName(register,exprType);

		    generator.write(generator.push(reg,exprType));
		}
		//Si es el identificador de una lista, hay que copiarlo
		else if ((expr.type.getType() instanceof ListType)&&
			 (expr instanceof Identifier)) {
		    String stack_p = generator.stack_pointer();

		    reg = generator.addrRegName(register);

		    ((Identifier)expr).currentDirection(generator);
		    
		    copyList(generator,expr.type,reg,register+1);
		}
		//Si es un tipo compuesto literal, ya se genero en la pila
		else{
		    //Se genera el valor
		    expr.tox86(generator);

		    reg = generator.regName(register,exprType);

		    generator.write(generator.push(reg,exprType.size()));
		}

		params_size += exprType.size();
	    }
	    //Caso por referencia
	    else{
		//Seteo el nombre correcto del registro a utilizar
		reg = generator.addrRegName(register);

		((Identifier)expr).currentDirection(generator);
		generator.write(generator.pushAddr(reg));

		params_size += generator.word_size();
	    }
		
	}

	//Llamada
	code += generator.call(routine.label);
	
	//Se desempilan los parametros
	code += generator.add(generator.stack_pointer(),
			      Integer.toString(params_size));

	//Se restauran los registros
	code += generator.restore_regs_caller(register);

	//Devolucion del argumento si es una funcion
	if (isFunction){
	    reg = generator.regName(register,((FunctionType)routine).getReturnType());
	    ax = generator.regName(0,((FunctionType)routine).getReturnType());
	    code += generator.mov(reg,ax);
	}

	generator.write(code);
    }

    public static void copyList(Genx86 generator,Type t,
				String listAddr,int free_register)
	throws IOException,InvalidCodeException{
	generator.save(free_register);

	Type listType = ((ListType)t.getType()).getInsideType();
	String auxReg = generator.regName(free_register,listType);
	String listTypeSize = Integer.toString(listType.size());
	int listSize = ((ListType)t.getType()).len();
	String listEnd = Integer.toString((listSize-1)*listType.size());

	//Apunto al final de la lista ya que, como se va a poner
	//en la pila, de otra forma quedaria alrevez
	generator.write(generator.add(listAddr,listEnd));

	for (int i = 0; i < listSize; i++) {
	    generator.write(generator.mov(auxReg,"["+listAddr+"]",listType));
	    generator.write(generator.push(auxReg,listType));
	    generator.write(generator.sub(listAddr,listTypeSize));
	}

	generator.restore(free_register);
    }

    public static void copyDict(Genx86 generator,Type t,
				String dictAddr,int free_register)
	throws IOException,InvalidCodeException{
	generator.save(free_register);

	Type itemType;
	String itemTypeSize;
	String auxReg;
	Iterator it = ((DictType)t).getIterator();
	String dictEnd = Integer.toString(((DictType)t).size());

	//Apunto al final de la lista ya que, como se va a poner
	//en la pila, de otra forma quedaria alrevez
	generator.write(generator.add(dictAddr,dictEnd));

	while(it.hasNext()){
	    itemType = (Type)(it.next());
	    itemTypeSize = Integer.toString(itemType.size());
	    auxReg = generator.regName(free_register,itemType);

	    generator.write(generator.mov(auxReg,"["+dictAddr+"]",itemType));
	    generator.write(generator.push(auxReg,itemType));
	    generator.write(generator.sub(dictAddr,itemTypeSize));
	}

	generator.restore(free_register);
    }
}
