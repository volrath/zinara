package zinara.ast.instructions;

import zinara.ast.expression.Expression;

public abstract class Assignation extends Instruction {
    public abstract boolean isSingle();
    public abstract String toString();
}
