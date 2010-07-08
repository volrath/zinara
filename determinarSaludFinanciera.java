/*
 * Archivo: determinarSaludFinanciera.java
 *
 * Descripci'on: programa tal que dados un valor entero p, el capital inicial y, 
 *               y un arreglo v de p reales determina si los valores en v 
 *               corresponden a los movimientos de una empresa financieramente 
 *               saludable, y actualiza el capital y.
 *               Una empresa es considerada saludable si cada uno de los
 *               movimientos realizados son tales que no representan perdidas
 *               inferiores a 10% de capital inicial, y si el balance acumulado
 *               en los p movimientos es tal que es mayor estricto a 5% del
 *               capital inicial.
 *               Permite probar operaciones b'asicas sobre reales y booleanos,
 *               accesos a arreglo, iteraciones for y while sencillas.
 *               (problema tomado del examen parcial I del curso de algoritmos
 *                y estructuras I del trimestre septiembre-diciembre 2009)
 *
 * Fecha: 22 de junio de 2010
 *
 * Autora: 
 *
 */

class determinarSaludFinanciera {

    public static void main (String[] args) {

        /* inicializar en 12 en caso de s'olo manejar arreglos de tamaño 
           constante con valor conocido a momento de compilaci'on */
        final int p = Console.readInt("Valor de p: ");
        final double[] v = new double[p];
        double y = Console.readDouble("Capital inicial: ");
        boolean b;

        for (int i = 0; i < p; i++) {
            v[i] = Console.readDouble("Valor de v[" + i + "] : ");
        }

        System.out.println("La empresa tenia un capital inicial de " + y); 

        {
            double t;
            int k;
            String x;

            b = true;
            t = 0;
            k = 0;

            while ( k < p ) {

                b = b && (v[k] >= -0.1*y);
                t = t + v[k];
                k = k + 1;
            }

            b = (t > 0.05*y) && b;
            y = y + t;
            System.out.println("Su balance acumulado fue de " + t + ".");

            if (t > 0.05*y) {
                x = "";
            } else {
                x = "no ";
            }
            System.out.println("El balance acumulado " + x 
                              + "es mayor al 5% del capital inicial");
        }

        System.out.println("La empresa tiene un capital actual de " + y );
        if (b) {
            System.out.println("La empresa es saludable");
        } else {
            System.out.println("La empresa no es saludable");
        }
    }
}
