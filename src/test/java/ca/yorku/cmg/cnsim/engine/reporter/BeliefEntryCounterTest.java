/**
 * 
 */
package ca.yorku.cmg.cnsim.engine.reporter;

import static org.junit.jupiter.api.Assertions.*;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

/**
 * 
 */
class BeliefEntryCounterTest {

	protected BeliefEntryCounter beliefCounter = new BeliefEntryCounter();
	
	/**
	 * @throws java.lang.Exception
	 */
	@BeforeAll
	static void setUpBeforeClass() throws Exception {
	}

	/**
	 * @throws java.lang.Exception
	 */
	@AfterAll
	static void tearDownAfterClass() throws Exception {
	}

	/**
	 * @throws java.lang.Exception
	 */
	@BeforeEach
	void setUp() throws Exception {
		beliefCounter.add(1, 10, 130,1);
		beliefCounter.add(1, 10, 130,0);
		beliefCounter.add(1, 10, 140,1);
		
		beliefCounter.add(1, 20, 140,0.2F);
		beliefCounter.add(1, 20, 140,1);
		
		beliefCounter.add(1, 20, 180,1);
		beliefCounter.add(1, 30, 150,1);
		beliefCounter.add(1, 30, 150,0);	
	}

	/**
	 * @throws java.lang.Exception
	 */
	@AfterEach
	void tearDown() throws Exception {
	}

	/**
	 * Test method for {@link ca.yorku.cmg.cnsim.engine.reporter.BeliefEntryCounter#increment(int, long, long)}.
	 */
	@Test
	void testIncrement() {
		assertEquals(0.5, beliefCounter.getAverage(1, 10, 130), 0.0001);
		assertEquals(1.0, beliefCounter.getAverage(1, 10, 140), 0.0001);
		assertEquals(0.6, beliefCounter.getAverage(1, 20, 140), 0.0001);
		assertEquals(1.0, beliefCounter.getAverage(1, 20, 180), 0.0001);
		assertEquals(0.5, beliefCounter.getAverage(1, 30, 150), 0.0001);
	}

	/**
	 * Test method for {@link ca.yorku.cmg.cnsim.engine.reporter.BeliefEntryCounter#getEntries()}.
	 */
	@Test
	void testGetEntries() {
		//fail("Not yet implemented");
		String s = "";
		String target = "1, 10, 130, 0.5\n" +
				"1, 10, 140, 1.0\n" +
				"1, 20, 140, 0.6\n" +
				"1, 20, 180, 1.0\n" +
				"1, 30, 150, 0.5\n";
		for (String st : beliefCounter.getEntries()) {
			s= s + st + "\n"; 
		}
		assertEquals(target, s);
	}
	
}
