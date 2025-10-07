package ca.yorku.cmg.cnsim.engine;

/**
 * A quick way to way to add, enable and disable debug messages. 
 * TODO: allow writing to file.
 */
public class Debug {
	
    public static final String RESET  = "\u001B[0m";
    public static final String RED    = "\u001B[31m";
    public static final String GREEN  = "\u001B[32m";
    public static final String YELLOW = "\u001B[33m";
    public static final String BLUE   = "\u001B[34m";
    public static final String PURPLE = "\u001B[35m";
    public static final String CYAN   = "\u001B[36m";
    public static final String WHITE  = "\u001B[37m";
    public static final String BOLD      = "\u001B[1m";
    
	public static String toRed(String in) {
		return BOLD + RED + in + RESET;
	}
	
	public static String toCyan(String in) {
		return BOLD + CYAN + in + RESET;
	} 
	
	public static String toYellow(String in) {
		return BOLD + YELLOW + in + RESET;
	}
    
	private static int verbosityLevel = 1;
		
	public static void setVerboseLevel(int level) {
		if (level < 1 || level > 5) {
			throw new IllegalArgumentException("Debug verbosity level must be between 1 and 5");
		}
		Debug.verbosityLevel = level;
	}
	
	public static void p(String strings) {
		Debug.p(1, strings);
	}
	
	public static void p(int verLevel, String strings) {
		if (verLevel < 0) {
			throw new IllegalArgumentException("Debug verbosity level must be >= 0");
		}
		if (verLevel > 0 && verLevel <= Debug.verbosityLevel) {
			System.out.println(Debug.toCyan("[INFO]: ") + strings);
		}
	}
	
	public static void p(int verLevel, Object o, String strings) {
		Debug.p(verLevel, o.getClass().getSimpleName() + ": " + strings);
	}
	
	public static void e(String strings) {
		System.err.println(Debug.toRed("[ERR.]: ") + strings);
	}
	
	public static void e(Object o, String strings) {
		System.err.println(Debug.toRed("[ERR.]: ") + o.getClass().getSimpleName() + ": " + strings);
	}

	public static void w(String strings) {
		System.err.println(Debug.toYellow("[WARN]: ") + strings);
	}
	
	public static void w(Object o, String strings) {
		System.err.println(Debug.toRed("[WARN]: ") + o.getClass().getSimpleName() + ": " + strings);
	}
	
	
}
