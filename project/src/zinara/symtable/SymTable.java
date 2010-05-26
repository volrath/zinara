package zinara.symtable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Set;
import java.util.Iterator;

import zinara.ast.ASTNode;
import zinara.ast.Declaration;
import zinara.ast.SingleDeclaration;
import zinara.ast.MultipleDeclaration;
import zinara.ast.expression.Expression;
import zinara.ast.expression.LValue;
import zinara.ast.instructions.Assignation;
import zinara.ast.instructions.SingleAssignation;
import zinara.ast.instructions.MultipleAssignation;
import zinara.exceptions.IdentifierAlreadyDeclaredException;
import zinara.exceptions.IdentifierNotDeclaredException;
import zinara.exceptions.InvalidAssignationException;
import zinara.exceptions.TypeClashException;

public class SymTable{
    private HashMap table;
    private SymTable father;
    private ArrayList sons;    // ArrayList of symtables
    public String name = "";

    //@invariant table != null;
    //@invariant sons != null;

    public SymTable() {
	this.sons = new ArrayList();
	this.father = null;
	this.table = new HashMap();
    }

    public SymTable(SymTable f) {
	this.sons = new ArrayList();
	this.father = f;
	this.table = new HashMap();
    }

    public SymTable(SymTable f, String name) {
	this.sons = new ArrayList();
	this.father = f;
	this.table = new HashMap();
	this.name = name;
    }

    public boolean checkDoubleDeclaration(String id) throws IdentifierAlreadyDeclaredException {
	if (containsId(id))
	    throw new IdentifierAlreadyDeclaredException(id);
	else return false;
    }

    //@ requires decl != null;
    public void addDeclaration(Declaration decl) throws IdentifierAlreadyDeclaredException {
	SingleDeclaration current_decl;

	if (decl.isSingle()) {
	    //@ assume \typeof(decl) == \type(SingleDeclaration);
	    current_decl = (SingleDeclaration)decl;
	    if (!currentTableContainsId(current_decl.getId())) {
		addSymbol(current_decl.getId(),
			  new SymValue(current_decl.getType(), current_decl.isVariable()));
	    } else
		throw new IdentifierAlreadyDeclaredException(((SingleDeclaration)decl).getId());
	} else {
	    //@ assume \typeof(decl) == \type(MultipleDeclaration);
	    for (int i = 0; i < ((MultipleDeclaration)decl).size(); i++) {
		current_decl = ((MultipleDeclaration)decl).get(i);
		//@ assume current_decl != null;
		if (!currentTableContainsId(current_decl.getId())) {
		    addSymbol(current_decl.getId(), new SymValue(current_decl.getType(), current_decl.isVariable()));
		} else
		    throw new IdentifierAlreadyDeclaredException(current_decl.getId());
	    }
	}
    }

    public void addSymbol (String id, SymValue v){
	this.table.put(id,v);
    }

    public SymValue deleteSymbol (String id){
	return (SymValue)this.table.remove(id);
    }

    public SymValue getSymbol (String id){
	//@ assume \typeof(table.get(id)) == \type(SymValue);
	return (SymValue)this.table.get(id);
    }

    public SymTable getFather() { return this.father; }
    public ArrayList getSons() { return sons; }
    public SymTable getSon(int i) { return (SymTable)sons.get(i); }

    public boolean currentTableContainsId(String id){
	return this.table.containsKey(id);
    }

    public boolean containsId(String id) {
	if (this.table.containsKey(id)) return true;
	else if (father != null) return father.containsId(id);
	else return false;
    }

    public SymTable getSymTableForId(String id) {
	if (this.table.containsKey(id)) return this;
	else if (father != null) return father.getSymTableForId(id);
	else return null;
    }

    public SymTable getSymTableForIdOrDie(String id) throws IdentifierNotDeclaredException {
	SymTable t = getSymTableForId(id);
	if (t != null) return t;
	else throw new IdentifierNotDeclaredException(id);
    }

    public SymValue getSymValueForId(String id) {
	//@ assume \typeof(this.table.get(id)) == \type(SymValue);
	if (this.table.containsKey(id)) return (SymValue)this.table.get(id);
	else if (father != null) return father.getSymValueForId(id);
	else return null;
    }

    public SymValue getSymValueForIdOrDie(String id) throws IdentifierNotDeclaredException {
	SymValue sv = getSymValueForId(id);
	if (sv != null) return sv;
	else throw new IdentifierNotDeclaredException(id);
    }

    public boolean containsValue (SymValue v){
	return this.table.containsValue(v);
    }

    public boolean isEmpty (){
	return this.table.isEmpty();
    }
    
    public String toString() {
    	String ret = "";
    	for (int i = 0; i < sons.size(); i++)
    	    ret += (SymTable)sons.get(i) + ", ";
    	if (ret.length() != 0) ret = ret.substring(0, ret.length()-2);
    	return "<" + table.toString() + "[" + ret + "]>";
    }
    
    /*
      Checks two things, if the id of the assignation is declared and
      if the types match.
     */

    //@ requires expr != null;
    //@ requires lv != null;
    public SingleAssignation checkAssignation(LValue lv, Expression expr) 
	throws IdentifierNotDeclaredException, TypeClashException {
	//SymValue idSymValue = getSymValueForIdOrDie(id);

	//@ assume lv.getType() != null;

	if (lv.getType().getType().equals(expr.getType().getType()))
	    return new SingleAssignation(lv, expr);
	else
	    throw new TypeClashException("Conflicto de tipos entre el identificador " + lv + lv.getType() +" y la expresion " + expr + expr.getType());
    }

    /*
      Checks if the list of ids and expressions match in number, then
      checks the validity of every assignation issuing
      `checkAssignation`.
     */
    //@ requires ids != null;
    //@ requires exprs != null;
    //@ requires (\forall int i; i >=0 && i < ids.size(); \typeof(ids.get(i)) == \type(LValue));
    //@ requires (\forall int i; i >=0 && i < ids.size(); \typeof(ids.get(i)) == \type(Expression));
    public Assignation checkMultipleAssignations(ArrayList ids, ArrayList exprs)
	throws IdentifierNotDeclaredException, TypeClashException, InvalidAssignationException {
	if (ids.size() != exprs.size())
	    throw new InvalidAssignationException(); // FIX THIS: same as in MultipleAssignation.java

	if (ids.size() == 1)
	    return checkAssignation((LValue)ids.get(0), (Expression)exprs.get(0));
	else {
	    ArrayList assignations = new ArrayList();
	    for (int i = 0; i < ids.size(); i++)
		assignations.add(checkAssignation((LValue)ids.get(i), (Expression)exprs.get(i)));
	    return new MultipleAssignation(assignations);
	}
    }

    public SymTable newTable() {
	SymTable son = new SymTable(this);
	sons.add(son);
	return son;
    }

    //@requires son != null;
    public void addSon(SymTable son){
	this.sons.add(son);
    }

    public Set keySet() {
	return table.keySet();
    }
}