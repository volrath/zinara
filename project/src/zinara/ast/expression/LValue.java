package zinara.ast.expression;

import zinara.ast.expression.BooleanExp;
import zinara.code_generator.Genx86;
import zinara.exceptions.InvalidCodeException;
import zinara.exceptions.TypeClashException;

import java.io.IOException;

public abstract class LValue extends BooleanExp {
    public abstract void tox86(Genx86 generator) throws IOException, InvalidCodeException;

    public abstract void currentDirection(Genx86 generator) throws IOException, InvalidCodeException;

    public abstract boolean isConstant();
}
