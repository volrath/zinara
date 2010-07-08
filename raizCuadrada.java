/*
 * Archivo: raizCuadrada.java
 *
 * Descripci'on: programa tal que dado un real no negativo 'x' y una holgura 
 *               (real) 'e', determina la raiz cuadrada positiva 'y' aproximada 
 *               de 'x' con holgura 'e'.
 *               Esto corresponde a: | x - y*y | <= e /\ y >= 0.
 *               Permite probar operaciones b'asicas sobre reales y booleanos, y
 *               condicional e iteraci'on sencilla.
 *
 * Fecha: 21 de junio de 2010
 *
 */

class raizCuadrada {

    public static void main (String args[]) {

        final double x = Console.readDouble("Valor de x: ");
        final double e = Console.readDouble("Valor de la holgura permitida: ");
        double y =  -1;
        double z = 0;

        {

            double inf = 0;
            double sup = x + 1;

            boolean enc = false;

            while (inf != sup && !enc) {

                final double k = (inf + sup) / 2;

                if (k*k > x) {
                    z = k*k - x;
                } else {
                    z = x - k*k;
                }

                if (z <= e) {
                    inf = sup;
                    enc = true;
                    y = k;
                } else if (k*k > x) {
                    sup = k;
                } else if (x > k*k) {
                    inf = k;  
                }
            }
        }

        if (y*y > x) {
            z = y*y - x;
        } else {
            z = x - y*y;
        }

        System.out.println("El valor de la raiz aproximada de " + x + " es: "
                           + y + ". Se ha considerado una holgura maxima " 
                           + "permitida de " + e + ". El cuadrado de esta raiz " 
                           + "es " + (y*y) + " y su diferencia con " + x 
                           + " es " +z);
    }
}
