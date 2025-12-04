package ca.yorku.cmg.cnsim.engine.event;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.network.AbstractNetwork;
import ca.yorku.cmg.cnsim.engine.network.RandomEndToEndNetwork;
import ca.yorku.cmg.cnsim.engine.node.INode;
import ca.yorku.cmg.cnsim.engine.node.NodeSet;
import ca.yorku.cmg.cnsim.engine.node.NodeStub;
import ca.yorku.cmg.cnsim.engine.node.PoWNodeSet;

/**
 * Test class for {@link Event_BehaviorChange}.
 * 
 * @author Amirreza Radjou for the Conceptual Modeling Group @ York University
 */
class Event_BehaviorChangeTest {

	private Simulation sim;
	private NodeStub node;
	private String initialBehavior;
	private String newBehavior;
	private long eventTime;

	@BeforeEach
	void setUp() throws Exception {
		// Initialize Config for tests
		try {
			Config.init("src/test/resources/application.properties");
		} catch (Exception e) {
			// Config may already be initialized, ignore
		}
		
		// Create a simulation instance
		sim = new Simulation(1);
		
		// Create a node stub
		node = new NodeStub(sim);
		initialBehavior = "Honest";
		newBehavior = "Malicious";
		eventTime = 1000L; // 1000ms simulation time
		
		// Set initial behavior
		node.setBehavior(initialBehavior);
		
		// Set up a minimal network and NodeSet for the simulation
		// This is needed because super.happen() accesses sim.getNodeSet()
		NodeSet nodeSet = new PoWNodeSet(null) {
			@Override
			public void addNode() throws Exception {
				// Empty implementation for testing
			}
			
			@Override
			public void closeNodes() {
				// Empty implementation for testing
			}
		};
		// Use reflection to access protected field
		try {
			java.lang.reflect.Field nodesField = NodeSet.class.getDeclaredField("nodes");
			nodesField.setAccessible(true);
			java.util.ArrayList<INode> nodesList = new java.util.ArrayList<>();
			nodesList.add(node);
			nodesField.set(nodeSet, nodesList);
			
			AbstractNetwork network = new RandomEndToEndNetwork();
			java.lang.reflect.Field nsField = AbstractNetwork.class.getDeclaredField("ns");
			nsField.setAccessible(true);
			nsField.set(network, nodeSet);
			sim.setNetwork(network);
		} catch (Exception e) {
			// If reflection fails, tests may still work if they don't call super.happen()
			// or if they handle the null network gracefully
		}
	}

	@Test
	void testConstructor_basic() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime);
		
		assertNotNull(event);
		assertEquals(eventTime, event.getTime());
		assertEquals(newBehavior, event.getNewBehavior());
		assertEquals(initialBehavior, event.getOldBehavior());
		assertEquals(node, event.getNode());
		assertEquals(-1, event.getTargetTransactionID()); // Default value
	}

	@Test
	void testConstructor_withTargetTransactionID() {
		int targetTxID = 123;
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime, targetTxID);
		
		assertNotNull(event);
		assertEquals(newBehavior, event.getNewBehavior());
		assertEquals(targetTxID, event.getTargetTransactionID());
	}

	@Test
	void testHappen_changesBehaviorString() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime);
		
		// Verify initial behavior
		assertEquals(initialBehavior, node.getBehavior());
		
		// Execute the event
		event.happen(sim);
		
		// Verify behavior was changed
		assertEquals(newBehavior, node.getBehavior());
	}

	@Test
	void testHappen_preservesOldBehavior() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime);
		String oldBehavior = event.getOldBehavior();
		
		event.happen(sim);
		
		// Old behavior should still be accessible
		assertEquals(initialBehavior, oldBehavior);
		assertEquals(initialBehavior, event.getOldBehavior());
	}

	@Test
	void testHappen_multipleChanges() {
		String firstNewBehavior = "Selfish";
		String secondNewBehavior = "Honest";
		
		Event_BehaviorChange event1 = new Event_BehaviorChange(node, firstNewBehavior, eventTime);
		event1.happen(sim);
		assertEquals(firstNewBehavior, node.getBehavior());
		
		Event_BehaviorChange event2 = new Event_BehaviorChange(node, secondNewBehavior, eventTime + 100);
		event2.happen(sim);
		assertEquals(secondNewBehavior, node.getBehavior());
	}

	@Test
	void testHappen_sameBehavior() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, initialBehavior, eventTime);
		
		event.happen(sim);
		
		// Behavior should remain the same
		assertEquals(initialBehavior, node.getBehavior());
	}

	@Test
	void testHappen_assignsEventID() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime);
		
		// Before happen(), evtID should be 1 (default)
		assertEquals(1, event.getEvtID());
		
		event.happen(sim);
		
		// After happen(), evtID should be assigned
		assertTrue(event.getEvtID() > 0);
	}

	@Test
	void testHappen_callsSuperHappen() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime);
		
		// Verify that super.happen() is called (which assigns event ID)
		long evtIDBefore = event.getEvtID();
		event.happen(sim);
		long evtIDAfter = event.getEvtID();
		
		// Event ID should be assigned by super.happen()
		assertNotEquals(evtIDBefore, evtIDAfter);
		assertTrue(evtIDAfter > 0);
	}

	@Test
	void testGetNode() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime);
		
		INode retrievedNode = event.getNode();
		assertEquals(node, retrievedNode);
		assertSame(node, retrievedNode);
	}

	@Test
	void testGetNewBehavior() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime);
		
		assertEquals(newBehavior, event.getNewBehavior());
	}

	@Test
	void testGetOldBehavior() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime);
		
		assertEquals(initialBehavior, event.getOldBehavior());
	}

	@Test
	void testGetTargetTransactionID_default() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime);
		
		assertEquals(-1, event.getTargetTransactionID());
	}

	@Test
	void testGetTargetTransactionID_custom() {
		int targetTxID = 456;
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime, targetTxID);
		
		assertEquals(targetTxID, event.getTargetTransactionID());
	}

	@Test
	void testEventTime() {
		long customTime = 5000L;
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, customTime);
		
		assertEquals(customTime, event.getTime());
	}

	@Test
	void testEventTime_zero() {
		long zeroTime = 0L;
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, zeroTime);
		
		assertEquals(zeroTime, event.getTime());
	}

	@Test
	void testHappen_differentBehaviorTypes() {
		String[] behaviors = {"Honest", "Malicious", "Selfish", "Unknown"};
		
		for (String behavior : behaviors) {
			Event_BehaviorChange event = new Event_BehaviorChange(node, behavior, eventTime);
			event.happen(sim);
			assertEquals(behavior, node.getBehavior());
		}
	}

	@Test
	void testHappen_emptyBehaviorString() {
		String emptyBehavior = "";
		Event_BehaviorChange event = new Event_BehaviorChange(node, emptyBehavior, eventTime);
		
		event.happen(sim);
		
		assertEquals(emptyBehavior, node.getBehavior());
	}

	@Test
	void testConstructor_nullBehaviorString() {
		// Null behavior should throw IllegalArgumentException in constructor
		String nullBehavior = null;

		assertThrows(IllegalArgumentException.class, () -> {
			new Event_BehaviorChange(node, nullBehavior, eventTime);
		});
	}

	@Test
	void testHappen_withTargetTransactionID() {
		int targetTxID = 789;
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime, targetTxID);

		event.happen(sim);

		// Behavior should be changed
		assertEquals(newBehavior, node.getBehavior());
		// Target transaction ID should be stored
		assertEquals(targetTxID, event.getTargetTransactionID());
	}

	@Test
	void testConstructor_withConfirmationDelay() {
		int targetTxID = 100;
		int requiredConfirmations = 3;
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime, targetTxID, requiredConfirmations);

		assertNotNull(event);
		assertEquals(newBehavior, event.getNewBehavior());
		assertEquals(targetTxID, event.getTargetTransactionID());
		assertEquals(requiredConfirmations, event.getRequiredConfirmations());
		assertEquals(-1, event.getTargetTransactionBlockHeight()); // Not yet found
	}

	@Test
	void testConstructor_withZeroConfirmations() {
		int targetTxID = 100;
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime, targetTxID, 0);

		assertNotNull(event);
		assertEquals(0, event.getRequiredConfirmations());
	}

	@Test
	void testConstructor_confirmationDelayWithoutTargetTransaction() {
		// Should throw exception when requiredConfirmations > 0 but no target transaction
		assertThrows(IllegalArgumentException.class, () -> {
			new Event_BehaviorChange(node, newBehavior, eventTime, -1, 3);
		});
	}

	@Test
	void testConstructor_negativeConfirmations() {
		// Should throw exception for negative confirmations
		assertThrows(IllegalArgumentException.class, () -> {
			new Event_BehaviorChange(node, newBehavior, eventTime, 100, -1);
		});
	}

	@Test
	void testHappen_withZeroConfirmations() {
		// Zero confirmations should execute immediately (like the normal case)
		int targetTxID = 100;
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime, targetTxID, 0);

		// Verify initial behavior
		assertEquals(initialBehavior, node.getBehavior());

		// Execute the event
		event.happen(sim);

		// Behavior should be changed immediately
		assertEquals(newBehavior, node.getBehavior());
	}

	@Test
	void testGetRequiredConfirmations() {
		Event_BehaviorChange event1 = new Event_BehaviorChange(node, newBehavior, eventTime);
		assertEquals(0, event1.getRequiredConfirmations());

		Event_BehaviorChange event2 = new Event_BehaviorChange(node, newBehavior, eventTime, 100, 3);
		assertEquals(3, event2.getRequiredConfirmations());
	}

	@Test
	void testGetTargetTransactionBlockHeight() {
		Event_BehaviorChange event = new Event_BehaviorChange(node, newBehavior, eventTime, 100, 3);
		assertEquals(-1, event.getTargetTransactionBlockHeight()); // Initially not found
	}
}

