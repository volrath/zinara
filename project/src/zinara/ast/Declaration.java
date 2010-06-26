package zinara.ast;

import zinara.ast.ASTNode;
import zinara.ast.type.Type;

public abstract class Declaration extends ASTNode {
    public abstract boolean isSingle();
    public abstract String toString();
    public abstract Type getType();
}
