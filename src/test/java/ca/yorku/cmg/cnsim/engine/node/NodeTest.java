package ca.yorku.cmg.cnsim.engine.node;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

class NodeTest {

	private Node n; 

	NodeTest(){
		this.n = new NodeStub();
	}
	

	@BeforeEach
	void setUp() throws Exception {

	}

	@AfterEach
	void tearDown() throws Exception {
	}

	@Test
	void test_getNextTransmissionEndTime() {
		long nextT;
		
		nextT = n.getNextTransmissionEndTime(10, 5);
		n.setNetworkInterfaceBusyUntil(nextT);
		assertEquals(15, nextT);
		
		nextT = n.getNextTransmissionEndTime(11, 6);
		n.setNetworkInterfaceBusyUntil(nextT);
		assertEquals(21, nextT);

		nextT = n.getNextTransmissionEndTime(13, 3);
		n.setNetworkInterfaceBusyUntil(nextT);
		assertEquals(24, nextT);

		nextT = n.getNextTransmissionEndTime(27, 1);
		n.setNetworkInterfaceBusyUntil(nextT);
		assertEquals(28, nextT);

		nextT = n.getNextTransmissionEndTime(29, 2);
		n.setNetworkInterfaceBusyUntil(nextT);
		assertEquals(31, nextT);


		assertThrows(RuntimeException.class, () -> {
	    	n.getNextTransmissionEndTime(31, -2);
	    });
		
		assertThrows(RuntimeException.class, () -> {
	    	n.getNextTransmissionEndTime(-1, -2);
	    });

		
		assertThrows(RuntimeException.class, () -> {
	    	n.getNextTransmissionEndTime(-1, 5);
	    });
		
	}

}
