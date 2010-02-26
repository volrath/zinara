package zinara.ast.instructions;

import java.util.ArrayList;

public class MultipleAssignation extends Assignation {
    public ArrayList assignations;

    public boolean isSingle(){
	return false;
    }

    public MultipleAssignation(ArrayList as) { this.assignations = as; }
    public boolean add(SingleAssignation a) { return this.assignations.add(a); }
    public SingleAssignation get(int i) { return (SingleAssignation)this.assignations.get(i); }
}
