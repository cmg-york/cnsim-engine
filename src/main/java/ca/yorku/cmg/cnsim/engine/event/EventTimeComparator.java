package ca.yorku.cmg.cnsim.engine.event;

import java.util.Comparator;

 /**
 * Comparator for Event objects based on their scheduled time.
 * <p>
 * This comparator orders events in ascending order of their scheduled time.
 * If the time of the first event is greater than or equal to the second (i.e., happens later or at the same time), it returns 1; otherwise, it returns -1.
 * </p>
 * 
 * @see Event
 */
public class EventTimeComparator implements Comparator<Event>{
	
	
	/**
	 * Compares two Event objects based on their scheduled time.
	 * 
	 * @param e1 the first Event to be compared
	 * @param e2 the second Event to be compared
	 * @return 1 if the time of e1 is greater than or equal to the time of e2 (i.e., e1 happens after e2), -1 otherwise
	 */
	@Override
	public int compare(Event e1, Event e2) {
		if(e1.getTime() >= e2.getTime())
			return 1;
		else
			return -1;
	}
}
