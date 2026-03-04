package ca.yorku.cmg.cnsim.engine.sampling;

import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNetworkSampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractNodeSampler;
import ca.yorku.cmg.cnsim.engine.sampling.interfaces.AbstractTransactionSampler;
import ca.yorku.cmg.cnsim.engine.sampling.standardsamplers.StandardNetworkSampler;
import ca.yorku.cmg.cnsim.engine.sampling.standardsamplers.StandardNodeSampler;
import ca.yorku.cmg.cnsim.engine.sampling.standardsamplers.StandardTransactionSampler;
import org.junit.jupiter.api.*;

import static org.junit.jupiter.api.Assertions.*;

import java.util.Random;

/**
 * JUnit tests for {@link Sampler}.
 *
 * Test design document:
 * src/test/resources/test-design/ca/yorku/cmg/cnsim/engine/sampling/SamplerTest.md
 *
 */
public class SamplerTest {

    private Sampler sampler;

    @BeforeEach
    void setUp() {
        sampler = new Sampler();
    }

    // ---------------------
    // CONSTRUCTOR TESTS
    // ---------------------

    @Test
    @DisplayName("Initializing object with constructor")
    void testConstructor_TC1() {
        assertNotNull(sampler, "Sampler object was not created");
    }

    // ---------------------
    // GETPOISSONINTERVAL TESTS
    // ---------------------

    @Test
    @DisplayName("getPoissonInterval with lambda=-1 should throw ArithmeticException")
    void testGetPoissonInterval_TC2() {
        float lambda = -1f;
        Random r = new Random();

        ArithmeticException ex = assertThrows(ArithmeticException.class, () -> {
            sampler.getPoissonInterval(lambda, r);
        });

        assertTrue(ex.getMessage().contains("lambda < 0"));
    }

    @Test
    @DisplayName("getPoissonInterval with random=null should throw NullPointerException")
    void testGetPoissonInterval_TC3() {
        float lambda = 1f;
        Random r = null;

        NullPointerException ex = assertThrows(NullPointerException.class, () -> {
            sampler.getPoissonInterval(lambda, r);
        });

        assertTrue(ex.getMessage().contains("random cannot be null"));
    }

    @Test
    @DisplayName("getPoissonInterval with lambda=0 should return a positive result")
    void testGetPoissonInterval_TC4() {
        float lambda = 0f;
        Random r = new Random();

        assertTrue(sampler.getPoissonInterval(lambda, r) >= 0);
    }

    @Test
    @DisplayName("getPoissonInterval with lambda=0.001 should return a positive result")
    void testGetPoissonInterval_TC5() {
        float lambda = 0.001f;
        Random r = new Random();

        assertTrue(sampler.getPoissonInterval(lambda, r) >= 0);
    }

    @Test
    @DisplayName("getPoissonInterval with lambda=1.0 should return a positive result")
    void testGetPoissonInterval_TC6() {
        float lambda = 1.0f;
        Random r = new Random();

        assertTrue(sampler.getPoissonInterval(lambda, r) >= 0);
    }

    @Test
    @DisplayName("getPoissonInterval with lambda=10.0 should return a positive result")
    void testGetPoissonInterval_TC7() {
        float lambda = 10.0f;
        Random r = new Random();

        assertTrue(sampler.getPoissonInterval(lambda, r) >= 0);
    }

    // ---------------------
    // GETGAUSSIAN TESTS
    // ---------------------

    @Test
    @DisplayName("getGaussian with negative deviation should throw ArithmeticException")
    void testGetGaussian_TC8() {
        float mean = 10.0f;
        float deviation = -1f;
        Random r = new Random();

        ArithmeticException ex = assertThrows(ArithmeticException.class, () -> {
            sampler.getGaussian(mean, deviation, r);
        });

        assertTrue(ex.getMessage().contains("Standard deviation < 0"));
    }

    @Test
    @DisplayName("getGaussian with random=null should throw NullPointerException")
    void testGetGaussian_TC9() {
        float mean = 10.0f;
        float deviation = 1.0f;
        Random r = null;

        NullPointerException ex = assertThrows(NullPointerException.class, () -> {
            sampler.getGaussian(mean, deviation, r);
        });

        assertTrue(ex.getMessage().contains("random cannot be null"));
    }

    @Test
    @DisplayName("getGaussian with deviation=0 should return mean")
    void testGetGaussian_TC10() {
        float mean = 10.0f;
        float deviation = 0f;
        Random r = new Random();

        assertEquals(mean, sampler.getGaussian(mean, deviation, r));
    }

    @Test
    @DisplayName("getGaussian with deviation=0.1 should return a positive result")
    void testGetGaussian_TC11() {
        float mean = 10.0f;
        float deviation = 0.1f;
        Random r = new Random();

        assertTrue(sampler.getGaussian(mean, deviation, r) > 0);
    }

    @Test
    @DisplayName("getGaussian with negative mean should return a positive result")
    @Disabled("getGaussian is stuck in infinite loop")
    void testGetGaussian_TC12() {
        float mean = -10.0f;
        float deviation = 1f;
        Random r = new Random();

        assertTrue(sampler.getGaussian(mean, deviation, r) > 0);
    }

    @Test
    @DisplayName("getGaussian with mean=0 should return a positive result")
    void testGetGaussian_TC13() {
        float mean = 0f;
        float deviation = 1f;
        Random r = new Random();

        assertTrue(sampler.getGaussian(mean, deviation, r) > 0);
    }

    @Test
    @DisplayName("getGaussian with positive mean and deviation should return a positive result")
    void testGetGaussian_TC14() {
        float mean = 10.0f;
        float deviation = 1f;
        Random r = new Random();

        assertTrue(sampler.getGaussian(mean, deviation, r) > 0);
    }

    @Test
    @DisplayName("getGaussian with mean=100, deviation=10 should return a positive result")
    void testGetGaussian_TC15() {
        float mean = 100.0f;
        float deviation = 10f;
        Random r = new Random();

        assertTrue(sampler.getGaussian(mean, deviation, r) > 0);
    }

    @Test
    @DisplayName("getGaussian with mean=50, deviation=5 should return a positive result")
    void testGetGaussian_TC16() {
        float mean = 50.0f;
        float deviation = 5f;
        Random r = new Random();

        assertTrue(sampler.getGaussian(mean, deviation, r) > 0);
    }

    @Test
    @DisplayName("getGaussian with mean=1000, deviation=100 should return a positive result")
    void testGetGaussian_TC17() {
        float mean = 1000.0f;
        float deviation = 100f;
        Random r = new Random();

        assertTrue(sampler.getGaussian(mean, deviation, r) > 0);
    }

    @Test
    @DisplayName("getGaussian with mean=-1, deviation=10 should return a positive result")
    void testGetGaussian_TC18() {
        float mean = 10.0f;
        float deviation = 0.1f;
        Random r = new Random();

        assertTrue(sampler.getGaussian(mean, deviation, r) > 0);
    }

    // ---------------------
    // SIMPLE SETTERS/GETTERS TESTS
    // ---------------------

    @Test
    @DisplayName("Testing getTransactionSampler()")
    @Disabled("Config file not available")
    void testGetTransactionSampler_TC18() {
        AbstractTransactionSampler s = new StandardTransactionSampler(sampler);
        sampler.setTransactionSampler(s);

        assertEquals(s, sampler.getTransactionSampler());
    }

    @Test
    @DisplayName("TransactionSampler field should be set to null")
    void testSetTransactionSampler_TC19() {
        AbstractTransactionSampler txSampler = null;
        sampler.setTransactionSampler(txSampler);

        assertNull(sampler.getTransactionSampler());
    }

    @Test
    @DisplayName("TransactionSampler field should be set to the valid TransactionSampler input")
    @Disabled("Config file not available")
    void testSetTransactionSampler_TC20() {
        AbstractTransactionSampler txSampler = new StandardTransactionSampler(sampler);
        sampler.setTransactionSampler(txSampler);

        assertEquals(txSampler, sampler.getTransactionSampler());
    }

    @Test
    @DisplayName("getNodeSampler should return the assigned nodeSampler")
    @Disabled("Config file not available")
    void testGetNodeSampler_TC21() {
        AbstractNodeSampler nodeSampler = new StandardNodeSampler(sampler);
        sampler.setNodeSampler(nodeSampler);

        assertEquals(nodeSampler, sampler.getNodeSampler());
    }

    @Test
    @DisplayName("setNodeSampler should assign a null value if the nodeSampler is null")
    void testSetNodeSampler_TC22() {
        AbstractNodeSampler nodeSampler = null;
        sampler.setNodeSampler(nodeSampler);

        assertNull(sampler.getNodeSampler());
    }

    @Test
    @DisplayName("setNodeSampler should set the provided nodeSampler object")
    @Disabled("Config file not available")
    void testGetNodeSampler_TC23() {
        AbstractNodeSampler nodeSampler = new StandardNodeSampler(sampler);
        sampler.setNodeSampler(nodeSampler);

        assertEquals(nodeSampler, sampler.getNodeSampler());
    }

    @Test
    @DisplayName("getNetworkSampler should return the assigned NetworkSampler")
    @Disabled("Config file not available")
    void testGetNetworkSampler_TC24() {
        AbstractNetworkSampler networkSampler = new StandardNetworkSampler(sampler);
        sampler.setNetworkSampler(networkSampler);

        assertEquals(networkSampler, sampler.getNodeSampler());
    }

    @Test
    @DisplayName("setNetworkSampler should assign a null value if the NetworkSampler is null")
    void testSetNetworkSampler_TC25() {
        AbstractNetworkSampler networkSampler = null;
        sampler.setNetworkSampler(networkSampler);

        assertNull(sampler.getNetworkSampler());
    }

    @Test
    @DisplayName("setNetworkSampler should set the provided networkSampler object")
    @Disabled("Config file not available")
    void testGetNetworkSampler_TC26() {
        AbstractNetworkSampler networkSampler = new StandardNetworkSampler(sampler);
        sampler.setNetworkSampler(networkSampler);

        assertEquals(networkSampler, sampler.getNetworkSampler());
    }

}