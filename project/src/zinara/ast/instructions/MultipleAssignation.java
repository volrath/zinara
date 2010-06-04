package zinara.ast.instructions;

import java.io.IOException;
import java.util.ArrayList;

import zinara.code_generator.*;
import zinara.ast.expression.Expression;
import zinara.ast.expression.Identifier;
import zinara.exceptions.InvalidAssignationException;
import zinara.exceptions.InvalidCodeException;

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
	    asigs.add(new SingleAssignation(new Identifier((String)ids.get(i), null), (Expression)expressions.get(i)));
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
	    ret += " " + assignations.get(i);
	return "<MultipleAssignation:" + ret + ">";
    }

    public void tox86(Genx86 generate) throws IOException,InvalidCodeException{
	for (int i = 0; i < assignations.size(); i++)
	    ((SingleAssignation)assignations.get(i)).tox86(generate);
    }
}
