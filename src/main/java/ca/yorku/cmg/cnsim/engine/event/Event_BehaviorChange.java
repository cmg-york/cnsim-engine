package ca.yorku.cmg.cnsim.engine.event;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.node.INode;
import ca.yorku.cmg.cnsim.engine.reporter.Reporter;

/**
 * Represents an event that changes the behavior of a node in the simulation.
 * <p>
 * When this event occurs, the associated node's behavior is updated to the
 * new specified behavior type. This allows for dynamic changes in node behavior
 * during the simulation, such as switching from honest to malicious behavior,
 * or implementing other behavioral transitions.
 * </p>
 * <p>
 * For nodes that support behavior strategies (such as BitcoinNode), this event
 * will attempt to instantiate the appropriate behavior strategy based on the
 * behavior name. Currently supported behaviors include "Honest" and "Malicious"
 * for Bitcoin nodes.
 * </p>
 * <p>
 * The event can be scheduled at any simulation time to change a node's behavior
 * at that point in the simulation timeline.
 * </p>
 * <p>
 * Custom behavior strategies can be registered using the {@link #registerBehaviorStrategy(String, String, String)}
 * method. This allows extending the behavior system without modifying this class.
 * </p>
 *
 * @author Amirreza Radjou for the Conceptual Modeling Group @ York University
 * @see INode#setBehavior(String)
 * @see INode#getBehavior()
 * @see Reporter
 */
public class Event_BehaviorChange extends Event {

	/**
	 * Registry for behavior strategy mappings.
	 * Maps behavior names (case-insensitive) to their fully qualified class names.
	 */
	private static final java.util.Map<String, String> behaviorStrategyRegistry = new java.util.HashMap<>();

	// Initialize default behavior strategies
	static {
		registerBehaviorStrategy("Honest", "ca.yorku.cmg.cnsim.bitcoin.node", "HonestNodeBehavior");
		registerBehaviorStrategy("Malicious", "ca.yorku.cmg.cnsim.bitcoin.node", "MaliciousNodeBehavior");
	}

	/**
	 * Registers a behavior strategy class for a given behavior name.
	 * This allows extending the behavior system with custom strategies.
	 *
	 * @param behaviorName the behavior name (e.g., "Selfish", "Custom")
	 * @param packageName the package containing the strategy class
	 * @param className the simple class name of the strategy
	 */
	public static void registerBehaviorStrategy(String behaviorName, String packageName, String className) {
		if (behaviorName != null && packageName != null && className != null) {
			behaviorStrategyRegistry.put(behaviorName.toLowerCase(), packageName + "." + className);
		}
	}

	/**
	 * Clears all registered behavior strategies.
	 * Useful for testing or resetting the registry.
	 */
	public static void clearBehaviorStrategyRegistry() {
		behaviorStrategyRegistry.clear();
	}

	/** The node whose behavior will be changed. */
	private INode node;
	
	/** The new behavior type name (e.g., "Honest", "Malicious"). */
	private String newBehavior;
	
	/** The previous behavior type (for reporting purposes). */
	private String oldBehavior;
	
	/** Optional target transaction ID for MaliciousNodeBehavior (can be -1 if not applicable). */
	private int targetTransactionID;

	/** Number of block confirmations required after target transaction before behavior change (0 = immediate). */
	private int requiredConfirmations;

	/** Height of the block containing the target transaction (-1 if not yet found). */
	private int targetTransactionBlockHeight;
	
	/**
	 * Constructs a new {@code Event_BehaviorChange}.
	 *
	 * @param node the node whose behavior will be changed
	 * @param newBehavior the new behavior type name (e.g., "Honest", "Malicious")
	 * @param time the simulation time at which the event occurs
	 * @throws IllegalArgumentException if newBehavior is null
	 */
	public Event_BehaviorChange(INode node, String newBehavior, long time) {
		this(node, newBehavior, time, -1, 0);
	}
	
	/**
	 * Constructs a new {@code Event_BehaviorChange} with an optional target transaction ID
	 * for MaliciousNodeBehavior.
	 *
	 * @param node the node whose behavior will be changed
	 * @param newBehavior the new behavior type name (e.g., "Honest", "Malicious")
	 * @param time the simulation time at which the event occurs
	 * @param targetTransactionID the target transaction ID for MaliciousNodeBehavior (ignored for other behaviors)
	 * @throws IllegalArgumentException if newBehavior is null
	 */
	public Event_BehaviorChange(INode node, String newBehavior, long time, int targetTransactionID) {
		this(node, newBehavior, time, targetTransactionID, 0);
	}

	/**
	 * Constructs a new {@code Event_BehaviorChange} with confirmation delay support.
	 * <p>
	 * This constructor allows the behavior change to be delayed until a specified number
	 * of blocks have been confirmed after the target transaction. This is useful for
	 * simulating scenarios where behavior changes based on transaction confirmation depth.
	 * </p>
	 * <p>
	 * If requiredConfirmations is 0, the behavior change happens immediately when the event occurs.
	 * If requiredConfirmations > 0, the behavior change is delayed until that many blocks
	 * have been added to the blockchain after the block containing the target transaction.
	 * </p>
	 *
	 * @param node the node whose behavior will be changed
	 * @param newBehavior the new behavior type name (e.g., "Honest", "Malicious")
	 * @param time the simulation time at which the event occurs
	 * @param targetTransactionID the target transaction ID for tracking confirmations (required if requiredConfirmations > 0)
	 * @param requiredConfirmations the number of block confirmations to wait after target transaction (0 = immediate)
	 * @throws IllegalArgumentException if newBehavior is null or if requiredConfirmations > 0 but targetTransactionID < 0
	 */
	public Event_BehaviorChange(INode node, String newBehavior, long time, int targetTransactionID, int requiredConfirmations) {
		super();
		if (newBehavior == null) {
			throw new IllegalArgumentException("Behavior name cannot be null");
		}
		if (requiredConfirmations > 0 && targetTransactionID < 0) {
			throw new IllegalArgumentException("Target transaction ID must be specified when using confirmation delay");
		}
		if (requiredConfirmations < 0) {
			throw new IllegalArgumentException("Required confirmations cannot be negative");
		}
		this.node = node;
		this.newBehavior = newBehavior;
		this.oldBehavior = node.getBehavior();
		this.targetTransactionID = targetTransactionID;
		this.requiredConfirmations = requiredConfirmations;
		this.targetTransactionBlockHeight = -1; // Will be determined when transaction is found
		super.setTime(time);
	}
	
	/**
	 * Executes the event logic for changing a node's behavior.
	 * <p>
	 * This method updates the node's behavior to the new value. For BitcoinNode
	 * instances, it also attempts to set the appropriate behavior strategy.
	 * The event is logged to the reporter if event reporting is enabled.
	 * </p>
	 * <p>
	 * If confirmation delay is configured (requiredConfirmations > 0) for a
	 * MaliciousNodeBehavior, the confirmation requirement is set on the behavior
	 * strategy itself. The behavior will internally wait for the specified number
	 * of block confirmations before starting the attack, using a counter-based
	 * approach rather than event rescheduling.
	 * </p>
	 *
	 * @param sim the simulation instance in which the event occurs
	 * @see INode#setBehavior(String)
	 */
	@Override
	public void happen(Simulation sim) {
		super.happen(sim);

		// Update the node's behavior string
		node.setBehavior(newBehavior);
		
		// For BitcoinNode, also update the behavior strategy
		// We use reflection to avoid hard dependency on Bitcoin-specific classes
		try {
			// Check if the node has a setBehaviorStrategy method (BitcoinNode)
			java.lang.reflect.Method setBehaviorStrategyMethod =
				node.getClass().getMethod("setBehaviorStrategy",
					Class.forName("ca.yorku.cmg.cnsim.bitcoin.node.NodeBehaviorStrategy"));

			// Create the appropriate behavior strategy based on the behavior name
			Object strategy = createBehaviorStrategy(newBehavior, node);
			if (strategy != null) {
				setBehaviorStrategyMethod.invoke(node, strategy);

				// If changing to MaliciousNodeBehavior, set target transaction and confirmation delay
				if (newBehavior.equalsIgnoreCase("Malicious")) {
					// Set target transaction ID if provided
					if (targetTransactionID >= 0) {
						try {
							java.lang.reflect.Method setTargetTxMethod =
								strategy.getClass().getMethod("setTargetTransaction", int.class);
							setTargetTxMethod.invoke(strategy, targetTransactionID);
						} catch (Exception e) {
							// If setting target transaction fails, continue anyway
							// The behavior strategy has been set successfully
							System.err.println("Warning: Could not set target transaction for node " +
								node.getID() + " behavior '" + newBehavior + "': " + e.getMessage());
						}
					}

					// Set required confirmations before attack if specified
					if (requiredConfirmations > 0) {
						try {
							java.lang.reflect.Method setConfirmationsMethod =
								strategy.getClass().getMethod("setRequiredConfirmationsBeforeAttack", int.class);
							setConfirmationsMethod.invoke(strategy, requiredConfirmations);
						} catch (Exception e) {
							// If setting confirmations fails, log warning
							System.err.println("Warning: Could not set required confirmations for node " +
								node.getID() + " behavior '" + newBehavior + "': " + e.getMessage());
						}
					}
				}
			} else {
				// Strategy creation returned null - either no strategy registered or instantiation failed
				// This is acceptable for behaviors that don't have strategy implementations
			}
		} catch (NoSuchMethodException e) {
			// Node doesn't support behavior strategies (e.g., NodeStub for testing)
			// This is expected and acceptable - the behavior string has been set
		} catch (ClassNotFoundException e) {
			// NodeBehaviorStrategy interface not found
			// This is expected for non-Bitcoin node types
		} catch (Exception e) {
			// Unexpected error - log detailed warning but continue
			// The behavior string has been set successfully
			System.err.println("Warning: Unexpected error setting behavior strategy for node " +
				node.getID() + " to '" + newBehavior + "': " + e.getClass().getSimpleName() +
				" - " + e.getMessage());
		}
		
		// Report the event if reporting is enabled
		if (Reporter.reportsEvents()) {
			Reporter.addEvent(
				sim.getSimID(),
				getEvtID(),
				getTime(),
				System.currentTimeMillis() - Simulation.sysStartTime,
				this.getClass().getSimpleName(),
				node.getID(),
				-1L // No specific transaction or container involved
			);
		}
	}
	
	/**
	 * Creates a behavior strategy instance based on the behavior name.
	 * This method uses reflection to instantiate the appropriate strategy
	 * class for Bitcoin nodes. The strategy class is looked up in the
	 * behavior strategy registry.
	 *
	 * @param behaviorName the name of the behavior (e.g., "Honest", "Malicious")
	 * @param node the node instance
	 * @return the behavior strategy instance, or null if creation fails
	 */
	private Object createBehaviorStrategy(String behaviorName, INode node) {
		try {
			// Look up the fully qualified class name in the registry
			String fullyQualifiedClassName = behaviorStrategyRegistry.get(behaviorName.toLowerCase());

			if (fullyQualifiedClassName == null) {
				// No strategy registered for this behavior name
				return null;
			}

			// Use reflection to instantiate the strategy
			Class<?> strategyClass = Class.forName(fullyQualifiedClassName);
			java.lang.reflect.Constructor<?> constructor =
				strategyClass.getConstructor(node.getClass());
			return constructor.newInstance(node);

		} catch (Exception e) {
			// If we can't create the strategy, return null
			// The behavior string will still be set
			return null;
		}
	}


	/**
	 * Returns the node whose behavior is being changed.
	 *
	 * @return the node instance
	 */
	public INode getNode() {
		return node;
	}
	
	/**
	 * Returns the new behavior type that will be set.
	 *
	 * @return the new behavior type name
	 */
	public String getNewBehavior() {
		return newBehavior;
	}
	
	/**
	 * Returns the previous behavior type (before the change).
	 *
	 * @return the old behavior type name
	 */
	public String getOldBehavior() {
		return oldBehavior;
	}
	
	/**
	 * Returns the target transaction ID (if set for MaliciousNodeBehavior).
	 *
	 * @return the target transaction ID, or -1 if not set
	 */
	public int getTargetTransactionID() {
		return targetTransactionID;
	}

	/**
	 * Returns the number of block confirmations required before behavior change.
	 *
	 * @return the required confirmations, or 0 for immediate behavior change
	 */
	public int getRequiredConfirmations() {
		return requiredConfirmations;
	}

	/**
	 * Returns the height of the block containing the target transaction.
	 *
	 * @return the block height, or -1 if not yet found
	 */
	public int getTargetTransactionBlockHeight() {
		return targetTransactionBlockHeight;
	}
}

