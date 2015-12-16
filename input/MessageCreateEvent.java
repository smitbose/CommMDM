/* 
 * Copyright 2010 Aalto University, ComNet
 * Released under GPLv3. See LICENSE.txt for details. 
 */
package input;

import core.DTNHost;
import core.Message;
import core.World;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
/**
 * External event for creating a message.
 */
public class MessageCreateEvent extends MessageEvent {
	private int size;
	private int responseSize;
	private boolean is_multicast = false;
        int [] list;
	/**
	 * Creates a message creation event with a optional response request
	 * @param from The creator of the message
	 * @param to Where the message is destined to
	 * @param id ID of the message
	 * @param size Size of the message
	 * @param responseSize Size of the requested response message or 0 if
	 * no response is requested
	 * @param time Time, when the message is created
	 */
	public MessageCreateEvent(int from, int to, String id, int size,
			int responseSize, double time) {
		super(from,to, id, time);
		this.size = size;
		this.responseSize = responseSize;
	}
       //Sahil: Mulaticast feature
	public MessageCreateEvent(int from, int to, String id, int size,
			int responseSize, double time,boolean is_multicast,int list[]) {
		super(from,to, id, time);
		this.size = size;
		this.responseSize = responseSize;
                this.is_multicast = is_multicast;
                this.list = list;
                if(list.length<5)
                {
                int x =10;
                }
	}
	/**
	 * Creates the message this event represents. 
	 */
	@Override
	public void processEvent(World world) {
            int i=0;
                ArrayList<DTNHost> destination_list =  new ArrayList<DTNHost>();
                if(!this.is_multicast){
		DTNHost to = world.getNodeByAddress(this.toAddr);
		DTNHost from = world.getNodeByAddress(this.fromAddr);			
		
		Message m = new Message(from, to, this.id, this.size);
		m.setResponseSize(this.responseSize);
		from.createNewMessage(m);
                }
                else
                {
          	DTNHost to = world.getNodeByAddress(this.toAddr);
		DTNHost from = world.getNodeByAddress(this.fromAddr);
                from.is_multicast = true;
                for(i=0;i<list.length;i++)
                {
                destination_list.add(world.getNodeByAddress(list[i]));
                }
                if(destination_list.size()<5)
                {
                int x = 10;
                }
		Message m = new Message(from, to, this.id, this.size,destination_list);
		m.setResponseSize(this.responseSize);
		from.createNewMessage(m);
                }
	}
	
	@Override
	public String toString() {
		return super.toString() + " [" + fromAddr + "->" + toAddr + "] " +
		"size:" + size + " CREATE";
	}
}
