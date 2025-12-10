package ca.yorku.cmg.cnsim.engine.exceptions;

public class ConfigurationException extends RuntimeException {

	/**
	 * 
	 */
	private static final long serialVersionUID = -7958826101054444965L;

	public ConfigurationException(String message) {
        super(message);
    }

    public ConfigurationException(String message, Throwable cause) {
        super(message, cause);
    }
}
