package ca.yorku.cmg.cnsim.engine;

/**
 * A quick way to way to add, enable and disable debug messages. 
 * TODO: use this idea to generate a system of classes to control verbosity 
 * of non-debug messages. 
 */
public class Debug {
	private static boolean enabled = true;
	
	public static void p(String strings) {
		if (enabled) {
			System.out.println(strings);
		}
	}
	
	public static void enableDebug() {
		enabled = true;
	}
	
	public static void disableDebug() {
		enabled = false;
	}
}
