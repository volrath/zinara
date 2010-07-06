package zinara;

import zinara.ast.type.*;

import java.util.ArrayList;
import java.util.HashMap;

public class Test {
    public static void main(String argv[]) {
	ArrayList types = new ArrayList(), helper = new ArrayList();;

	helper.add(new IntType());
	helper.add(new CharType());

	types.add(new BoolType());
	types.add(new CharType());
	types.add(new DictType(new HashMap()));
	types.add(new FloatType());
	types.add(new FunctionType(helper, new FloatType(), null));
	types.add(new IntType());
	types.add(new StringType());
	types.add(new TupleType(helper));

	Type t;
	for (int i = 0; i < types.size(); i++) {
	    t = (Type)types.get(i);
	    System.out.println(t + ": ");
	    if (t.getType() instanceof BoolType) System.out.println("   BoolType");
	    else if (t instanceof CharType) System.out.println("   CharType");
	    else if (t instanceof DictType) System.out.println("   DictType");
	    else if (t instanceof FloatType) System.out.println("   FloatType");
	    else if (t instanceof FunctionType) System.out.println("   FunctionType");
	    else if (t instanceof IntType) System.out.println("   IntType");
	    else if (t instanceof ListType) System.out.println("   ListType");
	    else if (t instanceof StringType) System.out.println("   StringType");
	    else if (t instanceof TupleType) System.out.println("   TupleType");
	    else System.out.println("No type found...");
	}
    }
}
