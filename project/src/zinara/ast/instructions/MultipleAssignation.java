package zinara.ast.instructions;

import java.util.ArrayList;

import zinara.ast.expression.Expression;
import zinara.exceptions.InvalidAssignationException;

public class MultipleAssignation extends Assignation {
    public ArrayList assignations; // Array of SingleAssignation

    public boolean isSingle(){
	return false;
    }

    public MultipleAssignation(ArrayList as) { this.assignations = as; }
    public MultipleAssignation(ArrayList ids, ArrayList expressions) throws InvalidAssignationException {
	if (ids.size() != expressions.size()) throw new InvalidAssignationException(); // FIX THIS: it's missing some argument to InvalidAssignationException to tell whats the reason of its invalidness
	
	ArrayList asigs = new ArrayList();
	for (int i = 0 ; i < ids.size() ; ++i){
	    // FIX THIS: it should check types first!!
	    asigs.add(new SingleAssignation(((String)ids.get(i)),((Expression)expressions.get(i))));
	}
	this.assignations = asigs;
    }

    public boolean add(SingleAssignation a) { return this.assignations.add(a); }

    public SingleAssignation get(int i) { return (SingleAssignation)this.assignations.get(i); }

    public int size(){
	return this.assignations.size();
    }

    public String toString() {
	String ret = "";
	SingleAssignation currentAssignation;
	for (int i = 0; i < assignations.size(); i++)
	    ret += " " + assignations.get(0);
	return "<MultipleAssignation:" + ret + ">";
    }
}
