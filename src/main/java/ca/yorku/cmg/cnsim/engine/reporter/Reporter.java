package ca.yorku.cmg.cnsim.engine.reporter;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;

import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.node.Node;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;

/**
 * Provides centralized measurement and reporting for simulations.
 * <p>
 * The {@code Reporter} class is designed to be used via its static methods and handles
 * the creation, logging, and flushing of simulation data for different categories:
 * <ul>
 *   <li><b>Events:</b> Records every processed event.</li>
 *   <li><b>Transactions:</b> Records every transaction arrival.</li>
 *   <li><b>Nodes:</b> Records information about each node in the simulation, typically at the end.</li>
 *   <li><b>Network events:</b> Records network link events or bandwidth changes.</li>
 *   <li><b>Beliefs:</b> Records nodes' beliefs about transactions, including optional short-format reports.</li>
 *   <li><b>Errors:</b> Records runtime errors or issues during simulation execution.</li>
 * </ul>
 * Additional reporting (e.g., structure or custom metrics) can be implemented in other classes.
 * 
 * <p>
 * The class manages the log data in {@linkplain ArrayList} structures and flushes them to files
 * when requested. Log files are created in a simulation-specific directory, based on the
 * {@linkplain Config configuration} properties and a timestamped run identifier.
 * </p>
 * 
 * <p>
 * Reporting can be selectively enabled or disabled per category using the static setter methods:
 * {@linkplain #reportEvents(boolean)}, {@linkplain #reportTransactions(boolean)},
 * {@linkplain #reportNodes(boolean)}, {@linkplain #reportNetEvents(boolean)},
 * {@linkplain #reportBeliefs(boolean)}, and {@linkplain #reportBeliefsShort(boolean)}.
 * </p>
 * 
 * <p>
 * All flush methods write the corresponding log to a CSV file (or TXT for errors) in the
 * simulation output directory. File names include the run identifier to ensure uniqueness.
 * </p>
 * 
 * <p>
 * The class is thread-unsafe; concurrent modifications to log data should be externally synchronized
 * if multiple threads may report simultaneously.
 * </p>
 * TODO: concentrate all flushing in one method.
 * TODO: design conditionals. 
 * @author
 *   Sotirios Liaskos for the Conceptual Modeling Group @ York University
 *
 * @see Node
 * @see Transaction
 * @see Config
 */
public class Reporter {
	
	 /** Stores transaction arrival log lines. */
	protected static ArrayList<String> inputTxLog = new ArrayList<String>();
	 
	 /** Stores event log lines. */
	protected static ArrayList<String> eventLog = new ArrayList<String>();
	
	 /** Stores node log lines. */
	protected static ArrayList<String> nodeLog = new ArrayList<String>();
	
	/** Stores compact belief log lines. */
	protected static ArrayList<String> netLog = new ArrayList<String>();
	
	/** Stores belief log lines. */
	protected static ArrayList<String> beliefLog = new ArrayList<String>();
	
	/** Stores compact belief log lines. */
	protected static ArrayList<String> beliefLogShort = new ArrayList<String>();
	
	/** Counts belief entries for the short belief report. */
	protected static BeliefEntryCounter beliefCounter = new BeliefEntryCounter();
	
	/** Stores error log lines. */
	protected static ArrayList<String> errorLog = new ArrayList<String>();
	
	/** The unique identifier for the current simulation run, used in file naming. */
	protected static String runId;
	
	/** The root directory for all simulation output files. */
	protected static String path;
	
	/** The base directory for all simulation output files, configurable via {@code sim.output.directory}. Default is {@code ./log/} */
	protected static String root = "./log/";
	
 	/** Reporting control flags */
	protected static boolean reportEvents;
	protected static boolean reportTransactions;
	protected static boolean reportNodes;
	protected static boolean reportNetEvents;
	protected static boolean reportBeliefs;
	protected static boolean reportBeliefsShort;



	
	
	// -----------------------------------------------------------------
	// STATIC INITIALIZATION
	// -----------------------------------------------------------------
	
	
	// Static initialization block sets up paths, runId, and prepares log headers
	static {
		root = Config.getPropertyString("sim.output.directory");

		String label = "";
		if (Config.hasProperty("sim.experimentalLabel")) {
			label = Config.getPropertyString("sim.experimentalLabel") + " - ";
		}
		
		//ID the run
		DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy.MM.dd HH.mm.ss");  
		LocalDateTime now = LocalDateTime.now();
		runId = label + dtf.format(now);
		path = root + runId + "/";
		new File(path).mkdirs();
		FileWriter writer;
		try {
			writer = new FileWriter(root + "LatestFileName.txt");
			writer.write(runId + "\n");
			writer.close();
		} catch (IOException e) {e.printStackTrace();}
		
		//Prepare the reporting structures
		eventLog.add("SimID, EventID, SimTime, SysTime, EventType, Node, Object");
		inputTxLog.add("SimID, TxID, Size (bytes), Value (coins), ArrivalTime (ms)");
		nodeLog.add("SimID, NodeID, HashPower (GH/s), ElectricPower (W), ElectricityCost (USD/kWh), TotalCycles");
		netLog.add("SimID, From (NodeID), To (NodeID), Bandwidth (bps), Time (ms from start)");
		beliefLog.add("SimID, Node ID, Transaction ID, Believes, Time (ms from start)");
		beliefLogShort.add("SimID, Transaction ID, Time (ms from start), Belief");
	}
	
	
	
	
	// -----------------------------------------------------------------
	// Methods to enable/disable or query report categories
	// -----------------------------------------------------------------
	
	
	public static void reportEvents(boolean reportEvents) {
		Reporter.reportEvents = reportEvents;
	}

	public static void reportTransactions(boolean reportTransactions) {
		Reporter.reportTransactions = reportTransactions;
	}

	public static void reportNodes(boolean reportNodes) {
		Reporter.reportNodes = reportNodes;
	}

	public static void reportNetEvents(boolean reportNetEvents) {
		Reporter.reportNetEvents = reportNetEvents;
	}

	public static void reportBeliefs(boolean reportBeliefs) {
		Reporter.reportBeliefs = reportBeliefs;
	}

	public static void reportBeliefsShort(boolean reportBeliefsShort) {
		Reporter.reportBeliefsShort = reportBeliefsShort;
	}
	
	public static boolean reportsBeliefs() {
		return Reporter.reportBeliefs;
	}

	public static boolean reportsBeliefsShort() {
		return Reporter.reportBeliefsShort;
	}
	
	
	
	public static String getRunId() {
		return(runId);
	}
	
	
	// -----------------------------------------------------------------
	// LOGGING METHODS
	// -----------------------------------------------------------------
	
	
	
 	/**
	 * Adds an entry to the event log with information about the event.
	 * 
	 * @param simID The simulation ID.
	 * @param evtID The event ID.
	 * @param simTime The simulation time at which the event occurred.
	 * @param sysTime The system time at which the event was processed.
	 * @param evtType A string describing the type of event.
	 * @param nodeInvolved The ID of the node involved in the event, or -1 if none.
	 * @param objInvolved The ID of the object involved in the event (e.g., transaction ID), or -1 if none.
	 */    
	public static void addEvent(int simID, long evtID, long simTime, long sysTime, 
			String evtType, int nodeInvolved, long objInvolved) {
		if (Reporter.reportEvents)
			eventLog.add(simID + "," + 
					evtID + "," + 
					simTime + "," + 
					sysTime + "," +
					evtType + "," +
					nodeInvolved + "," +
					objInvolved);
	}

    /**
     * Adds a transaction entry to the transaction log.
     *
     * @param simID Simulation ID
     * @param txID Transaction ID
     * @param size Transaction size in bytes TODO: verify it is bytes
     * @param value Transaction value in tokens
     * @param simTime Simulation time of arrival
     */
	public static void addTx(int simID, long txID, float size, float value, long simTime) {
		if (Reporter.reportTransactions)
			inputTxLog.add(simID + "," +
					txID + "," + 
					size + "," +
					value + "," +
					simTime);
	}
	
	   /**
     * Adds a node entry to the node log.
     *
     * @param simID Simulation ID
     * @param nodeID Node ID
     * @param hashPower Hashing power in GH/s
     * @param electricPower Electric power usage in Watts
     * @param electricityCost Electricity cost in USD/kWh
     * @param totalCycles Total hash cycles performed by the node
     */
	public static void addNode(int simID, int nodeID, float hashPower, float electricPower, 
		float electricityCost, double totalCycles) {
			if (Reporter.reportNodes)
				nodeLog.add(simID + "," +
					nodeID + "," + 
					hashPower + "," +
					electricPower + "," +
					electricityCost + "," +
					totalCycles);
	}
	
	
	
	/**
	 * Adds an entry to the network log with information about an event that establishes 
	 * or updates the bandwidth between two nodes. 
	 * For static networks only initial network creation is reported here. 
	 * For dynamic networks any change in the bandwidth between two nodes is reported.
	 * Zero bandwidth means no link.  
	 * @param simID The simulation ID.
	 * @param from The node from which the link is established
	 * @param to The node to which the link is established
	 * @param bandwidth The speed of the link
	 * @param simTime The time at which the event happened
	 */
	public static void addNetEvent(int simID, int from, int to, float bandwidth, long simTime) {
		if (Reporter.reportNetEvents)
			netLog.add(simID + "," +
					from + "," + 
					to + "," +
					bandwidth + "," +
					simTime);
	}
	
	
    /**
     * Adds a belief entry for a node about a transaction. If {@code reportBeliefsShort} is enabled, the belief counter is also updated, to be later be used for a compact report.
     *
     * @param simID Simulation ID
     * @param node Node ID
     * @param tx Transaction ID
     * @param believes {@code true} if node believes transaction is valid/final, {@code false} otherwise
     * @param simTime Simulation time at which the belief is recorded
     * @see #reportBeliefsShort
     * @see BeliefEntryCounter
     */
	public static void addBeliefEntry(int simID, int node, long tx, boolean believes, long simTime) {
		if (Reporter.reportBeliefs) {
			beliefLog.add(simID + "," +
					node + "," + 
					tx + "," +
					believes + "," +
					simTime);
		}
		
		if (Reporter.reportBeliefsShort) {
			if (believes) {
				beliefCounter.increment(simID, tx, simTime);
			}
		}
	}
	
	
	/**
	 * Adds an entry to the error log.   
	 * @param errorMsg The custom error message.
	 */
	public static void addErrorEntry(String errorMsg) {
		errorLog.add(errorMsg);
	}
		
	
	
	// -----------------------------------------------------------------
	// FLUSH METHODS - write the logs to files
	// -----------------------------------------------------------------
	

    /**
     * Flushes (writes out and clears) all report buffers maintained by the simulation reporting subsystem.
     * <p>
     * This method triggers the flush operations for all built-in report categories,
     * including event, input, node, network, belief, error, and configuration reports.
     * It also invokes {@linkplain #flushCustomReports()} to handle any user-defined or extension reports.
     * </p>
     * <p>
     * This method is {@code final} to ensure that subclasses cannot override it and
     * potentially skip mandatory flush operations.
     * </p>
     *
     * <b>Implementation detail:</b> This method delegates to specific flush methods for each report type.  Subclasses should extend reporting functionality through {@link #flushCustomReports()},
     * not by overriding this method.
     */
	public static final void flushAll() {
		flushEvtReport();
		flushInputReport();
		flushNodeReport();
		flushNetworkReport();
		flushBeliefReport();
		flushErrorReport();
		flushConfig();
		flushCustomReports();
	}
	
    /**
     * Flushes any custom or extension-specific reports defined outside the core reporting system.
     * <p>
     * This method is a no-op by default but may be extended to include
     * additional report flush operations specific to custom modules or simulations.
     * </p>
     *
     * <b>Implementation detail:</b> Subclasses or extensions may override this method to implement their
     * own flushing behavior for additional report types.
     */
	public static void flushCustomReports() {
	}

	
	/**
	 * Save reporter's event log to file. File name is "EventLog - [Simulation Date Time].csv"
	 */
	public static void flushEvtReport() {
		if (Reporter.reportEvents) {
			FileWriter writer;
			try {
				writer = new FileWriter(path + "EventLog - " + runId + ".csv");
				for(String str: eventLog) {
					  writer.write(str + System.lineSeparator());
					}
				writer.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	/**
	 * Save reporter's transaction log to file. File name is "Input - [Simulation Date Time].csv"
	 */
	public static void flushInputReport() {
		if (Reporter.reportTransactions) {
			FileWriter writer;
			try {
				writer = new FileWriter(path + "Input - " + runId + ".csv");
				for(String str: inputTxLog) {
					  writer.write(str + System.lineSeparator());
					}
				writer.close();
			} catch (IOException e) {
				e.printStackTrace();
			} 
		}
	}
	
	
	/**
	 * Save reporter's node log to file. File name is "Nodes - [Simulation Date Time].csv"
	 */
	public static void flushNodeReport() {
		if (Reporter.reportNodes) {
			FileWriter writer;
			try {
				writer = new FileWriter(path + "Nodes - " + runId + ".csv");
				for(String str: nodeLog) {
					  writer.write(str + System.lineSeparator());
					}
				writer.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	
	/**
	 * Save reporter's network log to file. File name is "NetLog - [Simulation Date Time].csv"
	 */
	public static void flushNetworkReport() {
		if (Reporter.reportNetEvents) {
			FileWriter writer;
			try {
				writer = new FileWriter(path + "NetLog - " + runId + ".csv");
				for(String str: netLog) {
					  writer.write(str + System.lineSeparator());
					}
				writer.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	
	/**
	 * Save reporter's belief log to file. File name is "BeliefLog - [Simulation Date Time].csv"
	 */
	public static void flushBeliefReport() {
		FileWriter writer;
		
		if (Reporter.reportBeliefs) {
			try {
				writer = new FileWriter(path + "BeliefLog - " + runId + ".csv");
				for(String str: beliefLog) {
					  writer.write(str + System.lineSeparator());
					}
				writer.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}

		if (Reporter.reportBeliefsShort) {
			try {
				writer = new FileWriter(path + "BeliefLogShort - " + runId + ".csv");
				for(String str: beliefLogShort) {
					  writer.write(str + System.lineSeparator());
				}
				for(String str: beliefCounter.getEntries()) {
					  writer.write(str + System.lineSeparator());
				}
				writer.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
	}
	
	
	/**
	 * Save reporter's error log to file. File name is "ErrorLog - [Simulation Date Time].csv"
	 */
	public static void flushErrorReport() {
		FileWriter writer;
		boolean errorsExist = false;
		try {
			writer = new FileWriter(path + "ErrorLog - " + runId + ".txt");
			for(String str: errorLog) {
				writer.write(str + System.lineSeparator());
				errorsExist = true;
			}
			writer.close();
			if (errorsExist) {
				System.err.println("    Errors were produced. Please check " + path + "ErrorLog - " + runId + ".txt");
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	
	/**
	 * Export configuration. File name is "Config - [Simulation Date Time].csv"
	 */
	public static void flushConfig() {
		FileWriter writer;
		try {
			writer = new FileWriter(path + "Config - " + runId + ".csv");
			writer.write("Key, Value" + System.lineSeparator());
			writer.write(Config.printPropertiesToString());
			writer.close();
		} catch (IOException e) {
			e.printStackTrace();
		} 
	}
	
}
