package zinara.symtable;

import java.util.HashMap;
import java.util.Set;
import java.util.Iterator;

import zinara.ast.type.Type;
import zinara.exceptions.NewTypeException;

public class TypeTable {
    HashMap table; // HashMap of <String, Type>

    public TypeTable() { table = new HashMap(); }

    public void add(String id, Type t) { table.put(id, t); }

    public void createNewType(String id, Type baseType) throws NewTypeException {
	Type type = (Type)table.get(id);
	if (type != null)
	    throw new NewTypeException("El identificador '" + id + "' ya ha sido utilizado para definir un nuevo tipo " + type);
	baseType.setName(id);
	table.put(id, baseType);
    }

    public void createAlias(String id, Type t) throws NewTypeException {
	Type t1 = (Type)table.get(id);
	if (t1 != null)
	    throw new NewTypeException("El identificador '" + id + "' ya ha sido utilizado para definir un alias para el tipo " + t);
	table.put(id, t);
    }

    public Type get(String id) throws NewTypeException {
	Type type = (Type)table.get(id);
	if (type == null)
	    throw new NewTypeException("El identificador '" + id + "' no ha sido utilizado para definir ningun tipo en el programa actual");
	return type;
    }
}
