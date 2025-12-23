package ca.yorku.cmg.cnsim.engine.config;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Properties;

import ca.yorku.cmg.cnsim.engine.exceptions.ConfigurationException;

public class Config {
    static Properties prop = new Properties();
    static boolean initialized = false;
    static String configLabel = "";
    
    public static void init(String propFileName) throws FileNotFoundException {
    	
        File file = new File(propFileName);
        if (!file.exists()) {
            throw new FileNotFoundException(propFileName + " not found");
        }

        configLabel = file.getName();
        int dotIndex = configLabel.lastIndexOf('.');
        if (dotIndex > 0) {
			configLabel = configLabel.substring(0, dotIndex);
		}
        
        try (InputStream in = new FileInputStream(file)) {
            prop.load(in);
            initialized = true;
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(-1);
        }
    }
    
    /**
    public static void chk(String propertyKey) throws Exception {
    	if (!initialized) {
    		throw new Exception("Error: configuration file uninitialized.");
    	} else if (prop.getProperty(propertyKey) == null) {
    		throw new Exception("Error reading configuration file: property '" + propertyKey + "' does not exist.");
    	}
    } */

    public static void check(String propertyKey) {
    	if (!initialized) {
    		throw new ConfigurationException("Error: configuration file uninitialized.");
    	} else if (!prop.containsKey(propertyKey)) {
    		throw new ConfigurationException("Error reading configuration file: property '" + propertyKey + "' does not exist.");
    	}

    }
    

    /*
     * 
     * PROPERTY READING
     *  
     */

    
    public static String getProperty(String propertyKey) {
    	check(propertyKey);
    	return prop.getProperty(propertyKey);
    }
    
    
    public static int getPropertyInt(String propertyKey) {
    	int l; 
    	String val = getProperty(propertyKey);
    	try {
    		l =  Integer.parseInt(val);
    	} catch (NumberFormatException e) {
    		throw new ConfigurationException("Error reading configuration key: '" + propertyKey + "' as integer",e);
    	}
        return l;
     }
    
    public static long getPropertyLong(String propertyKey) {
    	long l; 
    	String val = getProperty(propertyKey);
    	try {
    		l =  Long.parseLong(val);
    	} catch (NumberFormatException e) {
    		throw new ConfigurationException("Error reading configuration key: '" + propertyKey + "' as long",e);
    	}
        return l;
     }
    
    public static Float getPropertyFloat(String propertyKey) {
    	float l; 
    	String val = getProperty(propertyKey);
    	try {
    		l =  Float.parseFloat(val);
    	} catch (NumberFormatException e) {
    		throw new ConfigurationException("Error reading configuration key: '" + propertyKey + "' as float",e);
    	}
        return l;
     }
 

    public static Double getPropertyDouble(String propertyKey) {
    	double l;
    	String val = getProperty(propertyKey);
    	try {
    		l =  Double.parseDouble(val);
    	} catch (NumberFormatException e) {
    		throw new ConfigurationException("Error reading configuration key: '" + propertyKey + "' as float",e);
    	}
        return l;
     }
    
	public static boolean getPropertyBoolean(String propertyKey) {

    	String val = getProperty(propertyKey);
    	
        if (val == null) {
            throw new ConfigurationException("Missing required boolean property: " + propertyKey);
        }
        
        val = val.trim();

        switch (val.toUpperCase()) {
            case "TRUE":
            case "T":
                return true;
            case "FALSE":
            case "F":
                return false;
            default:
                throw new ConfigurationException(
                    "Invalid boolean value for property '" + propertyKey + "': '" + val + "'. " +
                    "Expected true/false or T/F (case-insensitive)."
                );
        }
	}
	
	public static String getPropertyString(String propertyKey) {
		return(prop.getProperty(propertyKey,null));
	}

	
    /**
     * Takes a string of the form "{ID1, ID2, ...}" and returns a long array with the IDs.   
     * @param input A string of the form "{ID1, ID2, ...}", where ID1, ID2 are transaction IDs.
     * @return A long array of ID1, ID2, ... .  If input string is empty (""), or "{}", or null, 
     * return value is null.
     * @throws IllegalArgumentException if input string is malformed i.e., 
     *    (a) missing "{" or "}, 
     *    (b) any IDi is greater than workload.numTransactions TODO
     *    (c) any IDi is not numeric
     */
    public static long[] parseStringToArray(String input) {
        // Remove the curly braces and split the string by commas
    	
    	if (input.equals("")) return (new long[0]);
    	if (input.equals("{}")) return (new long[0]);
    	
    	if (!String.valueOf(input.charAt(input.length()-1)).equals("}")) throw new IllegalArgumentException("Error in configuration file, line with " + input + ": missing closing bracket.");
    	if (!String.valueOf(input.charAt(0)).equals("{")) throw new IllegalArgumentException("Error in configuration file, line with " + input + ": missing opening bracket.");
    	
    	
    	String trimmed = input.substring(1, input.length() - 1);
    	
        String[] parts = trimmed.split(",");

        for (int i = 0; i < parts.length; i++) {
            String element = parts[i];

            if (element == null || element.isEmpty()) {
                throw new IllegalArgumentException("Element at index " + i + " is null or empty.");
            }

            try {
                Integer.parseInt(element.trim()); // Attempt to parse the string as an integer
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("Invalid integer found at index " + i + ": '" + element + "'.");
            }
        }
        
        // Create an array to store the integers
        long[] result = new long[parts.length];
        
        // Parse each part to an integer and store it in the array
        for (int i = 0; i < parts.length; i++) {
            result[i] = Long.parseLong(parts[i].trim());
        }

        return result;
    }
	   
    
    public static boolean[] parseStringToBoolean(String input) {
        // Remove the curly braces and split the string by commas
        String trimmed = input.substring(1, input.length() - 1);
        String[] parts = trimmed.split(",");

        // Create an array to store the booleans
        boolean[] result = new boolean[parts.length];

        // Parse each part to a boolean and store it in the array
        for (int i = 0; i < parts.length; i++) {
            result[i] = Boolean.parseBoolean(parts[i].trim());
        }

        return result;
    }
    
    
    public static int[] parseStringToIntArray(String input) {
    	return (Arrays.stream(parseStringToArray(input)).
    			mapToInt(i -> (int) i).toArray());
    }
    

    public static void printProperties() {
        for (Object key: prop.keySet()) {
            System.out.println(key + ": " + prop.getProperty(key.toString()));
        }
    }
    
    public static String printPropertiesToString() {
    	String s = "";
        for (Object key: prop.keySet()) {
            s = s + key + "," + prop.getProperty(key.toString()) + System.lineSeparator();
        }
        return(s);
    }

	public static boolean hasProperty(String s) {
		return prop.containsKey(s);
	}
	
	public static String getConfigLabel() {
		return configLabel;
	}
	
	
}