package ca.yorku.cmg.cnsim.engine.transaction;

import java.util.List;

/**
 * Defines the main methods that a transaction containing type must include. Examples of ITxContainers include transaction pools and blocks.
 *
 * @author Sotirios Liaskos for the Conceptual Modelling Group, York University
 * 
 */

public interface ITxContainer {

    /**
     * Return the ID of the container
     *
     * @return The ID of the container
     */
    int getID();

    /**
     * Total number of transactions in the container.
     *
     * @return The number of transactions.
     */
    int getCount();

    /**
     * Total size in bytes contained in the container.
     * TODO: Are these bytes?
     *
     * @return The number of bytes in the container.
     */
    float getSize();

    /**
     * Total transaction value contained in the container.
     *
     * @return The total value of all transactions in the container.
     */
    float getValue();

    /**
     * Returns a list of transactions contained within this container.
     *
     * @return a list of transactions
     */
    List<Transaction> getTransactions();

    /**
     * Returns {@code true} if {@code Transaction t} is contained in the container.
     * Matching is based on ID.
     *
     * @param t The Transaction object in question
     * @return {@code true} if {@code t} is in the container, {@code false} otherwise.
     */
    boolean contains(Transaction t);

    /**
     * Returns {@code true} if transaction with id {@code txID} is contained in the container.
     *
     * @param txID The transaction ID in question
     * @return {@code true} if transaction with ID {@code txID} is in the container, {@code false} otherwise.
     */
    boolean contains(long txID);

    /**
     * Removes transactions from the group that are also contained in {@code g}.
     *
     * @param g The {@linkplain TransactionGroup} whose transactions are to be removed from the current group.
     */
    void extractGroup(TransactionGroup g);

    /**
     * Adds a transaction to the container.
     * Total size and value is updated.
     *
     * @param t The {@linkplain Transaction} object to be added.
     */
    void addTransaction(Transaction t);

    /**
     * Removes transaction from the container.
     * Total size and value is updated.
     *
     * @param t The {@linkplain Transaction} object to be removed.
     */
    void removeTransaction(Transaction t);

    /**
     * Remove the first transaction from the container and return a reference to the transaction just removed.
     * Total size and value is updated.
     *
     * @return A reference to the transaction removed.
     */
    Transaction removeNextTx();

    /**
     * Print the IDs of each transaction in the container.
     *
     * @param sep The separator between the IDs, e.g., ",".
     * @return A string with the list of IDs.
     */
    String printIDs(String sep);

}
