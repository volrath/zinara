package zinara.ast.type;

import java.util.ArrayList;

public class FunctionType extends Type {
    public ArrayList argsTypes; // arraylist of Type
    public Type returnType;

    public FunctionType(ArrayList al, Type rt) { this.argsTypes = al; this.returnType = rt; }
}
