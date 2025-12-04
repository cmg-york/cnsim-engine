package ca.yorku.cmg.cnsim.engine.node;

import ca.yorku.cmg.cnsim.engine.IStructure;
import ca.yorku.cmg.cnsim.engine.Simulation;
import ca.yorku.cmg.cnsim.engine.transaction.ITxContainer;
import ca.yorku.cmg.cnsim.engine.transaction.Transaction;

public class NodeStub extends Node {

	public NodeStub(Simulation sim) {
		super(sim);
		// TODO Auto-generated constructor stub
	}

	public NodeStub() {
		super();
	}

	
	
	@Override
	public IStructure getStructure() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void timeAdvancementReport() {
		// TODO Auto-generated method stub

	}

	@Override
	public void periodicReport() {
		// TODO Auto-generated method stub

	}

	@Override
	public void beliefReport(long[] sample, long time) {
		// TODO Auto-generated method stub

	}

	@Override
	public void nodeStatusReport() {
		// TODO Auto-generated method stub

	}

	@Override
	public void structureReport() {
		// TODO Auto-generated method stub

	}

	@Override
	public void close(INode n) {
		// TODO Auto-generated method stub

	}

	@Override
	public void event_NodeReceivesClientTransaction(Transaction t, long time) {
		// TODO Auto-generated method stub

	}

	@Override
	public void event_NodeReceivesPropagatedContainer(ITxContainer t) {
		// TODO Auto-generated method stub

	}

	@Override
	public void event_NodeCompletesValidation(ITxContainer t, long time) {
		// TODO Auto-generated method stub

	}

	@Override
	public void event_NodeReceivesPropagatedTransaction(Transaction t, long time) {
		// TODO Auto-generated method stub

	}

}
