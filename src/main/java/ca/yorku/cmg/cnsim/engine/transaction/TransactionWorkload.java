package ca.yorku.cmg.cnsim.engine.transaction;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import ca.yorku.cmg.cnsim.engine.sampling.Sampler;

/**
 * Represents a workload of transactions, which can be generated either from a file or using a sampler.
 * This class extends TransactionGroup and provides methods to add and manage transactions.
 * 
 * @author Sotirios Liaskos, Nahid Alimohammadi
 * @see TransactionGroup
 */
public class TransactionWorkload extends TransactionGroup {

    private Sampler sampler;
    private long timeEnd = 0;

   
    /**
     * Constructs a TransactionWorkload with the given sampler.
     * @param sampler The sampler used to generate transaction attributes.
     */
    public TransactionWorkload(Sampler sampler) {
        this.sampler = sampler;

    }
    
    /**
     * Adds a specified number of transactions from a given start time.
     * @param num The number of transactions to add.
     * @param startTime The start time of the first transaction.
     * @throws ArithmeticException If the start time or number of transactions is less than 0.
     * @throws Exception 
     */
    private void addTransactions(long num, long startTime) throws Exception{
    	if(startTime < 0)
    		throw new ArithmeticException("startTime < 0");
    	if(num < 0)
    		throw new ArithmeticException("num < 0");
        long currTime = startTime;

        for (long i = 1; i <= num; i++){
            try {
				currTime += (long) sampler.getTransactionSampler().getNextTransactionArrivalInterval();
			} catch (Exception e) {
				e.printStackTrace();
			}
            addTransaction(currTime);
        }
        timeEnd = currTime;
    }

    
    
    /**
     * Appends a specified number of transactions after the last transaction in the workload.
     * @param num The number of transactions to append.
     * @throws ArithmeticException If the number of transactions is less than 0.
     * @throws Exception  
     */
    public void appendTransactions(long num) throws Exception {
    	if(num < 0)
    		throw new ArithmeticException("num < 0");
        addTransactions(num, timeEnd);
    }
    
    /**
     * Adds a transaction with the given current time.
     * @param currTime The current time of the transaction.
     * @throws Exception 
     */
    public void addTransaction(long currTime) throws Exception{
        Transaction t;
        
        long trID = Transaction.getNextTxID();
        
        t = new Transaction(trID,
                currTime,
                sampler.getTransactionSampler().getNextTransactionFeeValue(),
                sampler.getTransactionSampler().getNextTransactionSize(),
                sampler.getTransactionSampler().getArrivalNode());
        
        if (trID == sampler.getTransactionSampler().getSeedChangeTx()) {
        	if (sampler.getTransactionSampler().seedUpdateEnabled()) {
            	t.makeSeedChanging();
            	sampler.getTransactionSampler().updateSeed();
        	}
        }
        
        addTransaction(t);
    }
    
	/**
	 * Picks a specified number of random transactions from the workload based on the given percentile value.
	 * @param transNo The number of transactions to pick.
	 * @param percentile The percentile value to determine the range for picking transactions. For example from 
	 * 100 transactions with indexes 1..100, percentile 0.25 will return samples from the first 25 transactions 
	 * (indexes 1..25)  
	 * @return An ArrayList of randomly picked transactions possibly with duplicates.
	 */
	public ArrayList<Transaction> pickRandomTransactions(int transNo,float percentile) {
		ArrayList<Transaction> rtx = new ArrayList<Transaction>();
		
		for (int i=1;i<=transNo;i++) {
			rtx.add(getTransaction(sampler.getTransactionSampler().getRandomNum(0, Math.round((getCount()-1)*percentile))));
		}
		return rtx;
	}

	/**
	 * Updates the given TxConflictRegistry with conflicts based on the specified dispersion and likelihood.
	 * @param reg The TxConflictRegistry to be updated.
	 * @param dispersion The dispersion parameter controlling the closeness of conflicts. In [0,1].
	 * @param likelihood The likelihood of a transaction having a conflict. In [0,1]
	 * @return The updated TxConflictRegistry.
	 */
	public void updateConflicts(
			TxConflictRegistry reg, 
			double dispersion, double likelihood) {
		
		System.err.print("I count: [");
		for (Transaction tx : getAllTransactions()) {
			if (reg.getMatch((int) tx.getID()) == -2) {
				int conflict = sampler.getTransactionSampler().getConflict(
						(int) tx.getID(),
						getAllTransactions().size(), 
						dispersion, likelihood);
				
				if ((conflict == -1) || (reg.getMatch(conflict) != -2)) {
					reg.noMatch((int) tx.getID());
					//System.err.print("(" + tx.getID() + " <-> " + -1 + "), ");
				} else {
					if (conflict <= tx.getID()) {
						throw new IllegalStateException("Conflicting ID must be larger than current tx ID");
					}
					reg.setMatch((int) tx.getID(), conflict);
					//System.err.print("(" + tx.getID() + " <-> " + conflict + "), ");
				}
			} else {
				//System.err.print("(" + tx.getID() + " <-> " + reg.getMatch((int) tx.getID()) + "), ");
			}
			
		}
		System.err.println("]");
	}

	
    //TODO Why did not used get group directly
	public List<Transaction> getAllTransactions() {
    	return getTransactions();
    }

	   
    
    /**
     * See {@linkplain TransactionGroup#TransactionGroup(String, boolean)} 
     * @param fileName The workload filename to be read.
     * @param hasHeader Whether the file has a header.
     * @throws Exception Generic IO exception.
     */
    public TransactionWorkload(String fileName, boolean hasHeader) throws Exception {
    	super(fileName, hasHeader);
    }

}
    
