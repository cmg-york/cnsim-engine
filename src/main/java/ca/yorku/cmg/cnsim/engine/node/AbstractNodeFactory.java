package ca.yorku.cmg.cnsim.engine.node;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.sampling.Sampler;

/**
 * Abstract factory class for creating {@link IMiner} instances.
 * <p>
 * Holds references to the {@link Simulation} and {@link Sampler} objects,
 * which can be used by subclasses to configure newly created nodes.
 * </p>
 * <p>
 * Subclasses must implement {@link #createNewNode()} to provide concrete
 * node creation logic.
 * </p>
 * 
 * @author Sotirios Liaskos for the Conceptual Modeling Group @ York University
 */
public abstract class AbstractNodeFactory {
	
    /**
     * The simulation instance associated with the factory.
     */
	protected Simulation sim;
	
    /**
     * The sampler container instance used for generating random behaviors or other sampling.
     */
	protected Sampler sampler;
	
    /**
     * Returns the simulation associated with this factory.
     *
     * @return the simulation instance
     */
	public Simulation getSim() {
		return sim;
	}

   /** Sets the simulation associated with this factory.
    *
    * @param sim the simulation instance
    */
	public void setSim(Simulation sim) {
		this.sim = sim;
	}

    /**
     * Returns the sampler associated with this factory.
     *
     * @return the sampler instance
     */
	public Sampler getSampler() {
		return sampler;
	}

    /**
     * Sets the sampler associated with this factory.
     *
     * @param sampler the sampler instance
     */
	public void setSampler(Sampler sampler) {
		this.sampler = sampler;
	}
	
    /**
     * Creates a new {@link INode} instance.
     * <p>
     * Concrete subclasses must implement this method to return a fully
     * initialized node. The creation logic may depend on the simulation
     * and sampler instances provided to the factory.
     * </p>
     *
     * @return a new node instance
     * @throws Exception if node creation fails
     */
	public abstract INode createNewNode() throws Exception;  
}
