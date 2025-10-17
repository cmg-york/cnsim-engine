package ca.yorku.cmg.cnsim.engine.node;

/**
 * Represents a network node within the simulation.
 * <p>
 * Each node has an associated structure (e.g., blockchain or DAG), 
 * a set of behavioral characteristics, and can report events for monitoring.
 * The interface defines methods for node properties,  
 * reporting, and event handling.
 * </p>
 * 
 * @author Sotirios
 */
public interface IMiner extends INode {
	
	
	// -----------------------------------------------------------------
	// GETTERS AND SETTERS
	// -----------------------------------------------------------------
	
    /**
     * Sets the total hash power of the node in Gigahashes per second (GH/s).
     *
     * @param hashPower the hash power in GH/s
     */
    public void setHashPower(float hashPower);

    /**
     * Returns the total hash power of the node in Gigahashes per second (GH/s).
     *
     * @return hash power in GH/s
     */
    public float getHashPower();

    /**
     * Sets the cost of electricity in tokens per kilowatt-hour (tokens/kWh).
     *
     * @param electricityCost the cost of electricity
     */
    public void setElectricityCost(float electricityCost);
    
    /**
     * Returns the cost of electricity in tokens per kilowatt-hour (tokens/kWh).
     *
     * @return the electricity cost
     */
    public float getElectricityCost();
    
    /**
     * Returns the cost in conventional currency tokens in tokens/GH. Calculation is as follows: 
     * [ [electrictiyCost ($/kWh) * electricPower (W) / 1000 (W/kW)] /  [3600 (s/h) * hashPower (GH/s)]] = 
     * [ [electrictiyCost ($/kWh) * electricPowerinkW (kW)] /  [3600 (s/h) * hashPower (GH/s)]] =
     * [ [electrictiyCostPerHour ($/h)] /  [hashesPerHour (GH/h)]] =
     * Tokens per billions of hashes ($/GH)
     * @return Cost in conventional currency tokens in tokens/GH.
     */
    public double getCostPerGH();
    
    
    /**
     * Returns the electric power of the node in Watts.
     *
     * @return electric power in Watts
     */
    public float getElectricPower();
    

    /**
     * Sets the electric power of the node in Watts.
     *
     * @param power the electric power in Watts
     */
    public void setElectricPower(float power);
    
     

    /**
     * Returns the total PoW cycles the node has expended
     * TODO: Unit of measure?
     * @return The total PoW cycles of the node has expended.
     */
    public double getTotalCycles();
    
	
	
	

    
    
}
