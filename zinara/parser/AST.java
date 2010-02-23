class AST{
    public class Program {
	private Main main;
	private Declaration declarations;
	
	public Program(Main m, Declaration d){
	    main=m;
	    declarations=d;
	}
    }

    public class Main{
	int i;
	
	public Main(){
	    i=0;
	}
    }

    public class Declaration{
	int i;
	
	public Declaration(){
	    i=0;
	}
    }
}