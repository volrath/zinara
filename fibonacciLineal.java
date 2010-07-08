/*
 * Archivo: fibonacciLineal.java
 *
 * Descripci'on: programa tal que dados un valor entero N, determina el
 *               fibonacci correspondiente fib.N. Esto con un orden de 
 *               complejidad lineal.
 *               Permite probar operaciones b'asicas sobre enteros y
 *               condicionales e iteraciones sencillas.
 *               (algoritmo tomado del cap'itulo 4 del texto "Programming: The
 *               derivation of algorithms" de Anne Kaldewaij)
 *
 * Fecha: 21 de junio de 2010
 *
 */

class fibonacciLineal {

    public static void main (String args[]) {

        final int N;
        int n, fib, fibSig;
        N = Console.readInt("Numero al que se le calcular'a el fibonacci: ");
        n = 0;
        fib = 0;
        fibSig = 1;

        while (n < N) {
            int tmp = fib;

            fib = fibSig;
            fibSig = tmp + fibSig;
            n = n + 1;
        }

        System.out.println("El numero de fibonacci de " + N + " es: " + fib);
    }
}
