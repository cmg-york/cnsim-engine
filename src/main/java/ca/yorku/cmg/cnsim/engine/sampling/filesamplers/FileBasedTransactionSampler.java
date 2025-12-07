package ca.yorku.cmg.cnsim.engine.sampling.filesamplers;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Queue;

import ca.yorku.cmg.cnsim.engine.Debug;
import ca.yorku.cmg.cnsim.engine.config.Config;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractTransactionSampler;

/**
 * Transaction sampler that reads transaction information from a CSV file.
 * <p>
 * The file is expected to contain transactions with the following columns:
 * <ol>
 *   <li>Transaction ID (ignored)</li>
 *   <li>Transaction size (long)</li>
 *   <li>Transaction fee (float)</li>
 *   <li>Transaction arrival time (long, milliseconds)</li>
 * </ol>
 * Optionally, the first line can be a header, which will be skipped.
 * <p>
 * If the file does not contain enough transactions as specified in the configuration
 * property {@code workload.numTransactions}, an optional {@linkplain AbstractTransactionSampler} 
 * can be used to supply additional transaction intervals, sizes, and fees.
 * 
 * @author Sotirios Liaskos
 * @see AbstractTransactionSampler
 */
public class FileBasedTransactionSampler extends AbstractTransactionSampler {
	
    /** Path to the CSV file containing the transaction workload */
    String transactionsFilePath;

    /** Optional alternative sampler for additional transactions if the file is too short */
    AbstractTransactionSampler alternativeSampler = null;

    /** Number of transactions required according to configuration */
    /** TODO-JIRA: Config validation */
    private int requiredTransactionLines = Config.getPropertyInt("workload.numTransactions");

    /** Arrival time of the last transaction (milliseconds) */
    private float lastArrivalTime = 0;

    /** Queue of transaction sizes read from file */
    private Queue<Long> transactionSizes = new LinkedList<>();

    /** Queue of transaction fees read from file */
    private Queue<Float> transactionFeeValues = new LinkedList<>();

    /** Queue of arrival node ids */
    private Queue<Integer> transactionNodeIDs = new LinkedList<>();
    
    /** Queue of transaction arrival times read from file (milliseconds) */
    private final Queue<Long> transactionArrivalTimes = new LinkedList<>();

    /** Queue of conflicting IDs */
    private ArrayList<Integer> conflictingTxs = new ArrayList<>();
    
    

    // -----------------------------------------------------------------
    // CONSTRUCTORS
    // -----------------------------------------------------------------

    /**
     * Creates a {@linkplain FileBasedTransactionSampler} that reads transactions from a file.
     * 
     * @param transactionsFilePath Path to the CSV file containing transaction data
     */
    public FileBasedTransactionSampler(String transactionsFilePath){
    	this.transactionsFilePath = transactionsFilePath;
    	try {
			loadTransactionWorkload();
		} catch (Exception e) {
			//TODO-JIRA: unified error reporting
			Debug.e(this, "Error loading workload: " + e.getMessage());
			throw new RuntimeException(e);
		}
    }
 
    /**
     * Creates a {@linkplain FileBasedTransactionSampler} with an alternative sampler.
     * <p>
     * The alternative sampler is used when the file does not contain enough transactions
     * as specified in configuration.
     * 
     * @param transactionsFilePath Path to the CSV file containing transaction data
     * @param randomSampler        Alternative {@linkplain AbstractTransactionSampler} for missing transactions
     */
    public FileBasedTransactionSampler(String transactionsFilePath, AbstractTransactionSampler randomSampler) {
    	this.alternativeSampler = randomSampler;
    	this.transactionsFilePath = transactionsFilePath;
    	try {
			loadTransactionWorkload();
		} catch (Exception e) {
			//TODO-JIRA: unified error reporting
			System.err.println("Error loading workload: " + e.getMessage());
			System.exit(-1);
		}
    }
    
    
    // -----------------------------------------------------------------
    // WORKLOAD LOADING
    // -----------------------------------------------------------------

    /**
     * Loads the transaction workload from the file.
     * 
     * @throws Exception if the file contains fewer transactions than required and no alternative sampler is defined
     */
    public void loadTransactionWorkload() throws Exception {
    	loadTransactionWorkload(true);
    }
    
    /**
     * Loads the transaction workload from the file, optionally skipping the header.
     * 
     * @param hasHeaders True if the first line is a header and should be skipped
     * @throws Exception if the file contains fewer transactions than required and no alternative sampler is defined
     * TODO: incorporate into centralized error and debug reporting.  

	public void loadTransactionWorkload(boolean hasHeaders) throws Exception {
		int lineCount = 0;
		String line;
		try (BufferedReader br = new BufferedReader(new FileReader(transactionsFilePath))) {
			while ((line = br.readLine()) != null) {
				lineCount++;
				String[] values = line.split(",");
				if (values.length != 4) {
					continue; // Skip lines that don't have exactly 4 values
				}
				if (hasHeaders && lineCount == 1) {
					continue; // Skip first line
				}
				try {
					transactionSizes.add(Long.parseLong(values[1].trim()));
					transactionFeeValues.add(Float.parseFloat(values[2].trim()));
					transactionArrivalTimes.add(Long.parseLong(values[3].trim()));
				} catch (NumberFormatException e) {
					System.err.println("Error parsing transaction line: " + line);
				}
			}
		} catch (IOException e) {
			Debug.e(this,"Error loading workload: no such file or directory.");
			throw e;
		}
		if (hasHeaders) lineCount--;
		if (lineCount < requiredTransactionLines) {
			if (alternativeSampler == null) {
				throw new Exception("The transaction file does not contain enough lines as per configuration file. Required: " + requiredTransactionLines + ", Found: " + lineCount + ". Define alternative sampler for the additional intervals or update config file.");
			} else {
				Debug.p(1,this,"The transaction file does not contain enough lines as per configuration file. Required: " + requiredTransactionLines + ", Found: " + lineCount + ". Additional arrrivals to be drawn from alternative sampler.");
			}
		} else if (lineCount > requiredTransactionLines) {
			Debug.w(this,"Transaction file contains more lines than required transactions as per configuration file. Required: "	+ requiredTransactionLines + ", Found: " + lineCount);
		}
	}
	*/
	
	
	
	public void loadTransactionWorkload(boolean hasHeaders) throws Exception {
	    int lineCount = 0;
	    String line;
	    try (BufferedReader br = new BufferedReader(new FileReader(transactionsFilePath))) {
	        while ((line = br.readLine()) != null) {
	            lineCount++;
	            String[] values = line.split(",");
	            
	            // Skip lines that don't have at least 4 columns
	            if (values.length < 5) {
	                continue;
	            }
	            
	            // Skip first line if headers
	            if (hasHeaders && lineCount == 1) {
	                continue;
	            }
	            
	            try {
	                transactionSizes.add(Long.parseLong(values[1].trim()));
	                transactionFeeValues.add(Float.parseFloat(values[2].trim()));
	                transactionNodeIDs.add(Integer.parseInt(values[3].trim()));
	                transactionArrivalTimes.add(Long.parseLong(values[4].trim()));

	                // Optional 5th column: conflictingTx
	                if (values.length >= 6) {
	                    try {
	                        conflictingTxs.add(Integer.parseInt(values[5].trim()));
	                    } catch (NumberFormatException e) {
	                        System.err.println("Error parsing conflictingTx for line: " + line + " — storing as -1");
	                        conflictingTxs.add(-1); // fallback if parsing fails
	                    }
	                } else {
	                    conflictingTxs.add(-1); // default if column missing
	                }
	                
	            } catch (NumberFormatException e) {
	                System.err.println("Error parsing transaction line: " + line);
	            }
	        }
	    } catch (IOException e) {
	        Debug.e(this,"Error loading workload: no such file or directory.");
	        throw e;
	    }

	    if (hasHeaders) lineCount--;
	    
	    if (lineCount < requiredTransactionLines) {
	        if (alternativeSampler == null) {
	            throw new Exception("The transaction file does not contain enough lines as per configuration file. Required: " + requiredTransactionLines + ", Found: " + lineCount + ". Define alternative sampler for the additional intervals or update config file.");
	        } else {
	            Debug.p(1,this,"The transaction file does not contain enough lines as per configuration file. Required: " + requiredTransactionLines + ", Found: " + lineCount + ". Additional arrivals to be drawn from alternative sampler.");
	        }
	    } else if (lineCount > requiredTransactionLines) {
	        Debug.w(this,"Transaction file contains more lines than required transactions as per configuration file. Required: " + requiredTransactionLines + ", Found: " + lineCount);
	    }
	}
	
	
	

	// -----------------------------------------------------------------
    // SAMPLING ROUTINES
    // -----------------------------------------------------------------

    /**
     * Returns the next transaction arrival interval in milliseconds.
     * <p>
     * Pulls from the file queues; if the file is exhausted, uses the alternative sampler.
     * </p>
     * 
     * @return interval until the next transaction in milliseconds
     * @throws Exception if the file is exhausted and no alternative sampler is defined
     */
    @Override
    public float getNextTransactionArrivalInterval() throws Exception {
    	float arrivalTime;
    	float interval;
    	
    	if (!transactionArrivalTimes.isEmpty()) {
    		arrivalTime = transactionArrivalTimes.poll();
    		interval = arrivalTime - lastArrivalTime;
    		lastArrivalTime = arrivalTime;
    	} else if (alternativeSampler != null) {
    		interval = alternativeSampler.getNextTransactionArrivalInterval();
    	} else {
    		Debug.e(this,"getNextTransactionArrivalInterval(): Transaction file has less transactions than specified in configuration file. Alternative Sampler not specified.");
    		throw new Exception("Transaction file has less transactions than specified in configuration file. Alternative Sampler not specified.");
    	}
        return (interval); 
    }

    /**
     * Returns the next transaction fee value.
     * <p>
     * Pulls from the file queues; if the file is exhausted, uses the alternative sampler.
     * </p>
     * 
     * @return transaction fee value
     * @throws Exception if the file is exhausted and no alternative sampler is defined
     */
    @Override
    public float getNextTransactionFeeValue() throws Exception {
    	if (!transactionFeeValues.isEmpty()) {
    		return(transactionFeeValues.poll());
    	} else if (alternativeSampler != null) {
    		return(alternativeSampler.getNextTransactionFeeValue());
    	} else {
    		Debug.e(this,"getNextTransactionFeeValue(): Transaction file has less transactions than specified in configuration file. Alternative Sampler not specified.");
    		throw new Exception("Transaction file has less transactions than specified in configuration file. Alternative Sampler not specified.");
    	}
    }

    /** 
    * Returns the next transaction size.
    * <p>
    * Pulls from the file queues; if the file is exhausted, uses the alternative sampler.
    * </p>
    * 
    * @return transaction size
    * @throws Exception if the file is exhausted and no alternative sampler is defined
    */
    @Override
    public long getNextTransactionSize() throws Exception {
    	if (!transactionSizes.isEmpty()) {
    		return(transactionSizes.poll());
    	} else if (alternativeSampler != null) {
    		return(alternativeSampler.getNextTransactionSize());
    	} else {
    		Debug.e(this,"getNextTransactionSize(): Transaction file has less transactions than specified in configuration file. Alternative Sampler not specified.");
    		throw new Exception("Transaction file has less transactions than specified in configuration file. Alternative Sampler not specified.");
    	}
    }
    

    
    /** 
     * Returns the next transaction size.
     * <p>
     * Pulls from the file queues; if the file is exhausted, uses the alternative sampler.
     * </p>
     * 
     * @return transaction size
     * @throws Exception if the file is exhausted and no alternative sampler is defined
     */
     @Override
     public int getArrivalNode() {
     	if (!transactionNodeIDs.isEmpty()) {
     		return(transactionNodeIDs.poll());
     	} else if (alternativeSampler != null) {
     		return(alternativeSampler.getArrivalNode());
     	} else {
     		Debug.e(this,"getArrivalNode(): Transaction file has less transactions than specified in configuration file. Alternative Sampler not specified.");
     		throw new IllegalStateException("Transaction file has less transactions than specified in configuration file. Alternative Sampler not specified.");
     	}
     }

    
    
    /**
     * Returns a uniformly sampled integer in the given range.
     * <p>
     * Delegates to the alternative sampler.
     * </p>
     */
    @Override
    public int getRandomNum(int min, int max) {
        return(alternativeSampler.getRandomNum(min, max));
    }

    
	@Override
	public int getConflict(int id, int N, double alpha, double likelihood) {
		int conf;
		if (id <= conflictingTxs.size()) {
			conf = conflictingTxs.get(id-1);
			//System.err.println("File conflict for  " + id + " is " + conf);
			return (conf);
		} else {
			conf = alternativeSampler.getConflict(id, N, alpha, likelihood);
			//System.err.println("Rand conflict for  " + id + " is " + conf);
			return (conf);
		}
	}
    
    
    
    
	// -----------------------------------------------------------------
    // SEED MANAGEMENT
    // -----------------------------------------------------------------

    
    /**
     * Updates the seed in the alternative sampler.
     * @see ca.yorku.cmg.cnsim.engine.sampling.interfaces.IMultiSowable#updateSeed()
     * @see ca.yorku.cmg.cnsim.engine.sampling.standardsamplers.StandardTransactionSampler#updateSeed()

     */
	@Override
	public void updateSeed() {
		alternativeSampler.updateSeed();
	}

    /**
     * Returns the transaction ID at which the seed will change.
     * <p>
     * Delegates to the alternative sampler.
     * </p>
     */
	@Override
	public long getSeedChangeTx() {
		return(alternativeSampler.getSeedChangeTx());
	}

    /**
     * Returns whether seed updates are enabled.
     * <p>
     * Delegates to the alternative sampler.
     * </p>
     */
	@Override
	public boolean seedUpdateEnabled() {
		return(alternativeSampler.seedUpdateEnabled());
	}



}
