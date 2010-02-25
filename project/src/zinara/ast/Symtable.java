package zinara.ast;

import java.util.*;

class Symtable{
    private Hashtable symtable;
    
    public Symtable(){
	this.symtable = new Hashtable();
    }

    public void addSymbol (String id, SymValue v){
	this.symtable.put(id,v);
    }

    public void delSymbol (String id){
	this.symtable.remove(id);
    }

    public Object getSymbol (String id){
	return this.symtable.get(id);
    }

    public boolean containsSymbol (String id){
	return this.symtable.containsKey(id);
    }

    public boolean containsValue (SymValue v){
	return this.symtable.containsValue(v);
    }

    public boolean empty (){
	return this.symtable.isEmpty();
    }
}