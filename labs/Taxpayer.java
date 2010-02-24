
/* 
   Daniel Barreto N. #04-36723
   ----------------------------------------------------------------------

   This assignment illustrates how specifications (esp invariants and 
   preconditions)  written in a formal language can help in removing 
   errors in code. 
   
   The assignment concerns a class "Taxpayer" that is used for taxpayers.
   
*/
class Taxpayer {
    
    /* FIELDS */
    
    /* isFemale is true iff the person is female */
    boolean isFemale;
    
    /* isMale is true iff the person is male */
    boolean isMale;
    
    Taxpayer father, mother; // These fields won't really be used until
    // the next part of the exercise.
    
    /* Age in years */ 
    int age; 
    
    boolean isMarried; 
    
    /* Reference to spouce if person is married, null otherwise */
    Taxpayer spouse;
    
    /* Constant default income tax allowance (belastingvrije som) */
    static final int DEFAULT_ALLOWANCE = 5000;
    
    /* Constant income tax allowance for Old Age Pensioners over 65 */
    static final  int ALLOWANCE_OAP = 7000;
    
    /* Income tax allowance (belastingvrije som) */
    int tax_allowance; 
    
    /* Income per year */
    int income; 
    
    /* CONSTRUCTOR */
    //@ invariant isFemale != isMale;
    //@ invariant isMarried ==> (spouse != null);
    Taxpayer(boolean jongetje, Taxpayer ma, Taxpayer pa) {
	age = 0;
	isMarried = false;
	this.isMale = jongetje;
	this.isFemale = !jongetje;
	mother = ma;
	father = pa;
	spouse = null;
	income = 0;
	tax_allowance = DEFAULT_ALLOWANCE;
	/* The line below makes explicit the assumption that a new Taxpayer is not 
	 * married to anyone yet. A bit silly of course, but we need this to keep 
	 * ESC/Java2 happy. */
	//@ assume (\forall Taxpayer p; p.spouse != this); 
    } 
    
    /* METHODS */
    
    /* Marry to new_spouse */
    //@ requires new_spouse != null;
    //@ requires (new_spouse.isFemale && this.isMale) || (new_spouse.isMale && this.isFemale);
    //@ ensures spouse != null;
    //@ ensures new_spouse.spouse == this;
    void marry(Taxpayer new_spouse) {
	new_spouse.spouse = this;
	spouse = new_spouse;
	isMarried = true;
    }
    
    /* Divorce from current spouse */
    //@ requires spouse != null;
    //@ requires spouse.spouse == this;
    //@ requires spouse != this;
    //@ ensures spouse == null && isMarried == false;
    //@ ensures \old(spouse).spouse == null && \old(spouse).isMarried == false;
    //@ ensures age < 65 && \old(tax_allowance) > DEFAULT_ALLOWANCE ==> tax_allowance == DEFAULT_ALLOWANCE && \old(spouse).tax_allowance == \old(spouse.tax_allowance) + (\old(tax_allowance) - DEFAULT_ALLOWANCE);
    //@ ensures age >= 65 && \old(tax_allowance) > ALLOWANCE_OAP ==> tax_allowance == ALLOWANCE_OAP && \old(spouse).tax_allowance == \old(spouse.tax_allowance) + (\old(tax_allowance) - ALLOWANCE_OAP);
    void divorce() {
	if (age < 65 && tax_allowance > DEFAULT_ALLOWANCE)
	    transferAllowance(tax_allowance - DEFAULT_ALLOWANCE);
	else
	    transferAllowance(tax_allowance - ALLOWANCE_OAP);

	spouse.isMarried = false;
	spouse.spouse = null;
	spouse = null;
	isMarried = false;
    }
    
    /* Transfer change of the tax allowance from this person to his/her spouse */
    //@ requires spouse != null;
    //@ requires spouse.spouse == this;
    //@ requires spouse != this;
    //@ ensures tax_allowance == \old(tax_allowance) - change;
    //@ ensures spouse.tax_allowance == \old(spouse.tax_allowance) + change;
    void transferAllowance(int change) {
	tax_allowance = tax_allowance - change;
	spouse.tax_allowance = spouse.tax_allowance + change;
    }
    
    /* Taxpayer has a birthday and the age increases by one */
    // @ensures age == \old(age) + 1;
    // @ensures age >= 65 ==> tax_allowance <= ALLOWANCE_OAP;
    // @ensures age < 65 ==> tax_allowance <= DEFAULT_ALLOWANCE;
    void haveBirthday() {
	age++;
    }
    
}
