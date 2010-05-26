package zinara.ast.instructions;

import zinara.ast.expression.Expression;
import zinara.code_generator.*;

import java.io.IOException;
public abstract class Assignation extends Instruction {
    public abstract boolean isSingle();
    public abstract String toString();
}
