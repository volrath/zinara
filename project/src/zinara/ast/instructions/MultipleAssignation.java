package zinara.ast.instructions;

import java.util.ArrayList;

import zinara.ast.expression.Expression;
import zinara.exceptions.InvalidAssignation;

public class MultipleAssignation extends Assignation {
    public ArrayList assignations; // Array of SingleAssignation

    public boolean isSingle(){
	return false;
    }

    public MultipleAssignation(ArrayList as) { this.assignations = as; }
    public MultipleAssignation(ArrayList ids, ArrayList expressions) throws InvalidAssignation {
	if (ids.size() != expressions.size()) throw new InvalidAssignation(); // FIX THIS: it's missing some argument to InvalidAssignation to tell whats the reason of its invalidness
	
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
}
