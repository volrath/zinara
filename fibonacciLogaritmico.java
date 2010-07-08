/*
 * Archivo: fibonacciLogaritmico.java
 *
 * Descripci'on: programa tal que dados un valor entero N, determina el
 *               fibonacci correspondiente fib.N. Esto con un orden de
 *               complejidad logaritmico.
 *               Permite probar operaciones b'asicas sobre enteros y
 *               condicionales e iteraciones sencillas.
 *               (algoritmo tomado del cap'itulo 5 del texto "Programming: The
 *               derivation of algorithms" de Anne Kaldewaij)
 *
 * Fecha: 27 de mayo de 2010
 *
 */

class fibonacciLogaritmico {

    public static void main (String args[]) {

        final int N;
        int x;
        N = Console.readInt("Valor de N: ");

        {

            int a, b, n, y;
            a = 0;
            b = 1;
            x = 0;
            y = 1;
            n = N;
           
            while ( n != 0 ) {

                if (n % 2 == 0) {
                    int aux = a;
                    a = a*a + b*b;
                    b = aux*b + b*aux + b*b;
                    n = n / 2;
                } else if (n % 2 == 1) {
                    int aux = x;
                    x = a*x + b*y;
                    y = b*aux + a*y + b*y;
                    n = n - 1;
                }
            } 
        }

        System.out.println("El valor de fibonacci de " + N + " es: " + x);
    }
}
