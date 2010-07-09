package zinara.code_generator;

import java.util.HashMap;

public class DataTranslator{
    
    public DataTranslator(){}

    public static String toASCII(char C){
	int asciiC = (int)C;
	return Integer.toString(asciiC);
    }

    public static String toReal(double D){
	return toDouble(D)+"h";
    }

    public static String toReal(float F){
	return toFloat(F)+"h";
    }

    public static String toDouble(double D){

	return Long.toHexString(Double.doubleToRawLongBits(D));
	// String d = "";

	// long bits;
	// long mask = 0x00000001;

	// bits = Double.doubleToLongBits(D);
	
	// for (int i=1 ; i<=64; ++i){
	//     d = Long.toString(bits & mask)+d;
	//     bits = bits >>> 1;
	// }
	
	// return toHex(d);
    }

    public static String toFloat(float F){
	return Integer.toHexString(Float.floatToRawIntBits(F));

	// String f = "";

	// int bits;
	// int mask = 0x0001;

	// bits = Float.floatToIntBits(F);
	
	// for (int i=1 ; i<=32; ++i){
	//     f = Integer.toString(bits & mask)+f;
	//     bits = bits >>> 1;
	// }
	
	// return toHex(f);
    }

    public static String toHex(String binary){
	String hex = "";
	int i = 0;
	
	while (i<=(binary.length())-4){
	    hex = hex + hexMap(binary.substring(i,i+4));
	    i += 4;
	}

	return hex;
    }

    public static String hexMap(String binary){	
	if (binary.compareTo("0000") == 0)
	    return "0";
	else if (binary.compareTo("0001") == 0)
	    return "1";
	else if (binary.compareTo("0010") == 0)
	    return "2";
	else if (binary.compareTo("0011") == 0)
	    return "3";
	else if (binary.compareTo("0100") == 0)
	    return "4";
	else if (binary.compareTo("0101") == 0)
	    return "5";
	else if (binary.compareTo("0110") == 0)
	    return "6";
	else if (binary.compareTo("0111") == 0)
	    return "7";
	else if (binary.compareTo("1000") == 0)
	    return "8";
	else if (binary.compareTo("1001") == 0)
	    return "9";
	else if (binary.compareTo("1010") == 0)
	    return "A";
	else if (binary.compareTo("1011") == 0)
	    return "B";
	else if (binary.compareTo("1100") == 0)
	    return "C";
	else if (binary.compareTo("1101") == 0)
	    return "D";
	else if (binary.compareTo("1110") == 0)
	    return "E";
	else if (binary.compareTo("1111") == 0)
	    return "F";
	else{
	    System.out.println("Invalid binary: "+binary);
	    System.exit(1);
	}
	return "";
    }
}