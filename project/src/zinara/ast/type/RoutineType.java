package zinara.ast.type;

import java.util.ArrayList;

import zinara.ast.instructions.CodeBlock;

public abstract class RoutineType extends Type {
    public ArrayList argsTypes; // arraylist of Type
    public CodeBlock codeBlock;
    public String label;
}
