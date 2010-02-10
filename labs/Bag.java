
/* ESC/Java2 Exercise: 
   
   This class implements a Bag of integers, using an array.

   Add JML specs to this class, to stop ESC/Java2 from complaining.

   However, beware that there are also errors in the code that you may
   have to fix to stop ESC/Java2 from complaining. (More generally, 
   feel free to improve the code to make it easier to specify in JML, 
   but _only_ do this if you think this makes the code better/easier 
   to understand.

   The only JML keywords needed for this are
      requires
      invariant 
      ensures 
  
   If you want, you can also use
      non_null
   as abbreviation.


   While developing your specs, it may be useful to use the keywords
      assert
   to add additional assertions in source code, to find out what 
   ESC/Java2 can - or cannot - prove at a given program point.
  
*/

public class Bag {

    int[] contents; //@ invariant contents != null;
    int n; //@ invariant n <= contents.length && n >= 0;

    //@ requires input != null;
    //@ requires input.length >= 0;
    //@ ensures contents.length == input.length;
    //@ ensures n == contents.length;
    // post: contenido de contents == contenido de input
    Bag(int[] input) {
	n = input.length;
	contents = new int[n];
	arraycopy(input, 0, contents, 0, n);
    }

    
    Bag() {
	n =0;
	contents = new int[0];
    }

    //@ requires n > 0;
    // post: el ene ke sale es igual al ene ke entro menos 1
    void removeOnce(int elt) {
	for (int i = 0; i < n; i++) {  
	    if (contents[i] == elt ) {
		n--;
		contents[i] = contents[n];
		int[] tmp = new int[n];
		arraycopy(contents, 0, tmp, 0, n);
		contents = tmp;
		return;
	    }
	}
    }

    //@ requires n > 0;
    void removeAll(int elt) {
	for (int i = 0; i < n; i++) {   
	    if (contents[i] == elt) {
		n--;
		contents[i] = contents[n];
	    }
	}
	int[] tmp = new int[n];
	arraycopy(contents, 0, tmp, 0, n);
	contents = tmp;
    }

    int getCount(int elt) {
	int count = 0;
	for (int i = 0; i < n; i++) 
	    if (contents[i] == elt) count++; 
	return count;
    }

    /* Warning: you may have a hard time checking the method "add" below.
       ESC/Java2 may warn about a very subtle bug that can be hard to spot. 
       If you cannot find the problem after staring at the code for an hour, 
       feel free to stop.
    */
    
    void add(int elt) {
	if (n == contents.length) {
	    int[] new_contents = new int[n > 0 ? 2*n : 1]; 
	    arraycopy(contents, 0, new_contents, 0, n);
	    contents = new_contents;
	}
	contents[n]=elt;
	n++;
    }

    //@ requires b != null && b.contents != null;
    void add(Bag b) {
	int[] new_contents = new int[n + b.n];
	arraycopy(contents, 0, new_contents, 0, n);
	arraycopy(b.contents, 0, new_contents, n, b.n);
	contents = new_contents;
    }

    //@ requires a != null;
    void add(int[] a) {
	this.add(new Bag(a));
    }

    //@ requires b != null && b.contents != null;
    Bag(Bag b) {
	contents = new int[b.n];
	this.add(b);
    }


    //@ requires src != null;
    //@ requires dest != null;
    //@ requires srcOff >= 0 && srcOff <= src.length;
    //@ requires destOff >= 0 && destOff <= dest.length;
    //@ requires length + srcOff <= src.length;
    //@ requires length + destOff <= dest.length;
    // post: contenido de dest y src desde srcoff y destoff iguales
    private static void arraycopy(int[] src,
				  int   srcOff,
				  int[] dest,
				  int   destOff,
				  int   length) {
	for( int i=0 ; i<length; i++) {
	    dest[destOff+i] = src[srcOff+i];
	}
    }
  
}
