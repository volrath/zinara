package zinara.symtable;

import java.util.Hashtable;
import java.util.ArrayList;

import zinara.ast.Declaration;
import zinara.ast.SingleDeclaration;
import zinara.ast.MultipleDeclaration;
import zinara.ast.expression.Expression;
import zinara.ast.instructions.Assignation;
import zinara.ast.instructions.SingleAssignation;
import zinara.ast.instructions.MultipleAssignation;
import zinara.exceptions.IdentifierAlreadyDeclaredException;
import zinara.exceptions.IdentifierNotDeclaredException;
import zinara.exceptions.InvalidAssignation;
import zinara.exceptions.TypeClashException;

public class SymTable{
    private Hashtable table;
    private SymTable father;
    public String name = "";
    
    public SymTable() {
	this.father = null;
	this.table = new Hashtable();
    }

    public SymTable(SymTable f) {
	this.father = f;
	this.table = new Hashtable();
    }

    public SymTable(SymTable f, String name) {
	this.father = f;
	this.table = new Hashtable();
	this.name = name;
    }

    public boolean checkDoubleDeclaration(String id) throws IdentifierAlreadyDeclaredException {
	if (containsId(id))
	    throw new IdentifierAlreadyDeclaredException(id);
	else return false;
    }

    public void addDeclaration(Declaration decl) throws IdentifierAlreadyDeclaredException {
	SingleDeclaration current_decl;
	if (decl.isSingle()) {
	    current_decl = (SingleDeclaration)decl;
	    if (containsId(current_decl.getId())) {
		addSymbol(current_decl.getId(),
			  new SymValue(current_decl.getType(), current_decl.isVariable()));
	    } else
		throw new IdentifierAlreadyDeclaredException(((SingleDeclaration)decl).getId());
	} else {
	    for (int i = 0; i < ((MultipleDeclaration)decl).size(); i++) {
		current_decl = ((MultipleDeclaration)decl).get(i);
		if (containsId(current_decl.getId())) {
		    addSymbol(current_decl.getId(),
			      new SymValue(current_decl.getType(), current_decl.isVariable()));
		} else
		    throw new IdentifierAlreadyDeclaredException(current_decl.getId());
	    }
	}
    }

    public void addSymbol (String id, SymValue v){
	this.table.put(id,v);
    }

    public void deleteSymbol (String id){
	this.table.remove(id);
    }

    public SymValue getSymbol (String id){
	return (SymValue)this.table.get(id);
    }

    public SymValue getSymbolOrDie(String id) throws IdentifierNotDeclaredException {
	if (!table.containsKey(id)) throw new IdentifierNotDeclaredException();
	return (SymValue)table.get(id);
    }

    public SymTable getFather (){
	return this.father;
    }

    public boolean containsId (String id){
	return this.table.containsKey(id);
    }

    public boolean containsIdOrDie(String id) throws IdentifierNotDeclaredException {
	if (containsId(id)) return true;
	else throw new IdentifierNotDeclaredException(id);
    }

    public boolean containsValue (SymValue v){
	return this.table.containsValue(v);
    }

    public boolean isEmpty (){
	return this.table.isEmpty();
    }

    public String toString() {
	return this.table.toString();
    }

    /*
      Checks two things, if the id of the assignation is declared and
      if the types match.
     */
    public SingleAssignation checkAssignation(String id, Expression expr) 
	throws IdentifierNotDeclaredException, TypeClashException {
	SymValue idSymValue = getSymbolOrDie(id);

	if (idSymValue.getType() == expr.getType())
	    return new SingleAssignation(id, expr);
	else
	    throw new TypeClashException(id);
    }

    /*
      Checks if the list of ids and expressions match in number, then
      checks the validity of every assignation issuing
      `checkAssignation`.
     */
    public Assignation checkMultipleAssignations(ArrayList ids, ArrayList exprs)
	throws IdentifierNotDeclaredException, TypeClashException, InvalidAssignation {
	if (ids.size() != exprs.size())
	    throw new InvalidAssignation(); // FIX THIS: same as in MultipleAssignation.java
	if (ids.size() == 1)
	    return checkAssignation((String)ids.get(0), (Expression)exprs.get(0));
	else {
	    ArrayList assignations = new ArrayList();
	    for (int i = 0; i < ids.size(); i++)
		assignations.add(checkAssignation((String)ids.get(i), (Expression)exprs.get(i)));
	    return new MultipleAssignation(assignations);
	}
    }
}