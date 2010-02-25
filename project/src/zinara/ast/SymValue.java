package zinara.ast;

class SymValue{
    private Object value;
    private String type;

    public SymValue(Object v, String t) {
        this.value = v;
        this.type = t;
    }

    public Object getValue(){
        return this.value;
    }

    public String getType() {
        return this.type;
    }
}