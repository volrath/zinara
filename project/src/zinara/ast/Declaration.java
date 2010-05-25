package zinara.ast;

import zinara.ast.ASTNode;

public abstract class Declaration extends ASTNode {
    public abstract boolean isSingle();
    public abstract String toString();
}
