package zinara.ast;
import zinara.code_generator.*;

public abstract class Declaration {
    public abstract boolean isSingle();
    public abstract String toString();
    public abstract String tox86(Genx86 generate);
}
