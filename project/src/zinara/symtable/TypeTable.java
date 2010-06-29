package zinara.symtable;

import java.util.HashMap;
import java.util.Set;
import java.util.Iterator;

import zinara.ast.type.Type;
import zinara.exceptions.NewTypeException;

public class TypeTable {
    HashMap table;

    public TypeTable() { table = new HashMap(); }

    public void add(String id, Type t) { table.put(id, t); }
    public void checkAndAdd(String id, Type t) throws NewTypeException {
	Type t1 = (Type)table.get(id);
	if (t1 != null)
	    throw new NewTypeException("El identificador '" + id + "' ya ha sido utilizado para definir el tipo " + t);
	table.put(id, t);
    }

    public Type get(String id) throws NewTypeException {
	Type type = (Type)table.get(id);
	if (type == null)
	    throw new NewTypeException("El identificador '" + id + "' no ha sido utilizado para definir ningun tipo en el programa actual");
	return type;
    }
}
