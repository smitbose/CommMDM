package routing;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import routing.decisionengine.MDMDecisionEngine;
import core.Application;
import core.Connection;
import core.DTNHost;
import core.Message;
import core.MessageListener;
import core.Settings;
import core.SimClock;
import core.SimError;
import core.Tuple;

/**
 * This class overrides ActiveRouter in order to inject calls to a 
 * DecisionEngine object where needed add extract as much code from the update()
 * method as possible. 
 * 
 * <strong>Forwarding Logic:</strong> 
 * 
 * A DecisionEngineRouter maintains a List of Tuple<Message, Connection> in 
 * support of a call to ActiveRouter.tryMessagesForConnected() in 
 * DecisionEngineRouter.update(). Since update() is called so frequently, we'd 
 * like as little computation done in it as possible; hence the List that gets
 * updated when events happen. Four events cause the List to be updated: a new 
 * message from this host, a new received message, a connection goes up, or a 
 * connection goes down. On a new message (either from this host or received 
 * from a peer), the collection of open connections is examined to see if the
 * message should be forwarded along them. If so, a new Tuple is added to the
 * List. When a connection goes up, the collection of messages is examined to 
 * determine to determine if any should be sent to this new peer, adding a Tuple
 * to the list if so. When a connection goes down, any Tuple in the list
 * associated with that connection is removed from the List.
 * 
 * <strong>Decision Engines</strong>
 * 
 * Most (if not all) routing decision making is provided by a 
 * RoutingDecisionEngine object. The DecisionEngine Interface defines methods 
 * that enact computation and return decisions as follows:
 * 
 * <ul>
 *   <li>In createNewMessage(), a call to RoutingDecisionEngine.newMessage() is 
 * 	 made. A return value of true indicates that the message should be added to
 * 	 the message store for routing. A false value indicates the message should
 *   be discarded.
 *   </li>
 *   <li>changedConnection() indicates either a connection went up or down. The
 *   appropriate connectionUp() or connectionDown() method is called on the
 *   RoutingDecisionEngine object. Also, on connection up events, this first
 *   peer to call changedConnection() will also call
 *   RoutingDecisionEngine.doExchangeForNewConnection() so that the two 
 *   decision engine objects can simultaneously exchange information and update 
 *   their routing tables (without fear of this method being called a second
 *   time).
 *   </li>
 *   <li>Starting a Message transfer, a protocol first asks the neighboring peer
 *   if it's okay to send the Message. If the peer indicates that the Message is
 *   OLD or DELIVERED, call to RoutingDecisionEngine.shouldDeleteOldMessage() is
 *   made to determine if the Message should be removed from the message store.
 *   <em>Note: if tombstones are enabled or deleteDelivered is disabled, the 
 *   Message will be deleted and no call to this method will be made.</em>
 *   </li>
 *   <li>When a message is received (in messageTransferred), a call to 
 *   RoutingDecisionEngine.isFinalDest() to determine if the receiving (this) 
 *   host is an intended recipient of the Message. Next, a call to 
 *   RoutingDecisionEngine.shouldSaveReceivedMessage() is made to determine if
 *   the new message should be stored and attempts to forward it on should be
 *   made. If so, the set of Connections is examined for transfer opportunities
 *   as described above.
 *   </li>
 *   <li> When a message is sent (in transferDone()), a call to 
 *   RoutingDecisionEngine.shouldDeleteSentMessage() is made to ask if the 
 *   departed Message now residing on a peer should be removed from the message
 *   store.
 *   </li>
 * </ul>
 * 
 * <strong>Tombstones</strong>
 * 
 * The ONE has the the deleteDelivered option that lets a host delete a message
 * if it comes in contact with the message's destination. More aggressive 
 * approach lets a host remember that a given message was already delivered by
 * storing the message ID in a list of delivered messages (which is called the
 * tombstone list here). Whenever any node tries to send a message to a host 
 * that has a tombstone for the message, the sending node receives the 
 * tombstone.
 * 
 * @author PJ Dillon, University of Pittsburgh
 */
public class DecisionEngineRouter extends ActiveRouter
{
	public static final String PUBSUB_NS = "DecisionEngineRouter";
	public static final String ENGINE_SETTING = "decisionEngine";
	public static final String TOMBSTONE_SETTING = "tombstones";
	public static final String CONNECTION_STATE_SETTING = "";
	
	protected boolean tombstoning;
	protected RoutingDecisionEngine decider;
	protected List<Tuple<Message, Connection>> outgoingMessages;
	
	protected Set<String> tombstones;
	
	/** 
	 * Used to save state machine when new connections are made. See comment in
	 * changedConnection() 
	 */
	protected Map<Connection, Integer> conStates;
	
	public DecisionEngineRouter(Settings s)
	{
		super(s);
		
		Settings routeSettings = new Settings(PUBSUB_NS);
		
		outgoingMessages = new LinkedList<Tuple<Message, Connection>>();
		
		decider = (RoutingDecisionEngine)routeSettings.createIntializedObject(
				"routing." + routeSettings.getSetting(ENGINE_SETTING));
		
		if(routeSettings.contains(TOMBSTONE_SETTING))
			tombstoning = routeSettings.getBoolean(TOMBSTONE_SETTING);
		else
			tombstoning = false;
		
		if(tombstoning)
			tombstones = new HashSet<String>(10);
		conStates = new HashMap<Connection, Integer>(4);
	}

	public DecisionEngineRouter(DecisionEngineRouter r)
	{
		super(r);
		outgoingMessages = new LinkedList<Tuple<Message, Connection>>();
		decider = r.decider.replicate();
		tombstoning = r.tombstoning;
		
		if(this.tombstoning)
			tombstones = new HashSet<String>(10);
		conStates = new HashMap<Connection, Integer>(4);
	}

	//@Override
	public MessageRouter replicate()
	{
		return new DecisionEngineRouter(this);
	}

	@Override
	public boolean createNewMessage(Message m)
	{
		if(decider.newMessage(m))
		{
			if(m.getId().equals("M14"))
				System.out.println("Host: " + getHost() + "Creating M14");
			makeRoomForNewMessage(m.getSize());
			addToMessages(m, true);
			
			findConnectionsForNewMessage(m, getHost());
			return true;
		}
		return false;
	}
	
	
	
	@Override
	public void connectionUp(Connection con)
	{
		DTNHost myHost = getHost();
		DTNHost otherNode = con.getOtherNode(myHost);
		DecisionEngineRouter otherRouter = (DecisionEngineRouter)otherNode.getRouter();
		
		decider.connectionUp(myHost, otherNode);
		
		/*
		 * This part is a little confusing because there's a problem we have to
		 * avoid. When a connection comes up, we're assuming here that the two 
		 * hosts who are now connected will exchange some routing information and
		 * update their own based on what the get from the peer. So host A updates
		 * its routing table with info from host B, and vice versa. In the real
		 * world, A would send its *old* routing information to B and compute new
		 * routing information later after receiving B's *old* routing information.
		 * In ONE, changedConnection() is called twice, once for each host A and
		 * B, in a serial fashion. If it's called for A first, A uses B's old info
		 * to compute its new info, but B later uses A's *new* info to compute its
		 * new info.... and this can lead to some nasty problems. 
		 * 
		 * To combat this, whichever host calls changedConnection() first calls
		 * doExchange() once. doExchange() interacts with the DecisionEngine to
		 * initiate the exchange of information, and it's assumed that this code
		 * will update the information on both peers simultaneously using the old
		 * information from both peers.
		 */
		if(shouldNotifyPeer(con))
		{
			this.doExchange(con, otherNode);
			otherRouter.didExchange(con);
		}
		
		/*
		 * Once we have new information computed for the peer, we figure out if
		 * there are any messages that should get sent to this peer.
		 */
		Collection<Message> msgs = getMessageCollection();
		for(Message m : msgs)
		{
			if(decider.shouldSendMessageToHost(m, otherNode))
				outgoingMessages.add(new Tuple<Message,Connection>(m, con));
		}
	}
	
	

	@Override
	public void connectionDown(Connection con)
	{
		DTNHost myHost = getHost();
		DTNHost otherNode = con.getOtherNode(myHost);
		//DecisionEngineRouter otherRouter = (DecisionEngineRouter)otherNode.getRouter();
		
		decider.connectionDown(myHost, otherNode);
		
		conStates.remove(con);
		
		/*
		 * If we  were trying to send message to this peer, we need to remove them
		 * from the outgoing List.
		 */
		for(Iterator<Tuple<Message,Connection>> i = outgoingMessages.iterator(); 
				i.hasNext();)
		{
			Tuple<Message, Connection> t = i.next();
			if(t.getValue() == con)
				i.remove();
		}
	}

	/*@Override
	public void changedConnection(Connection con)
	{
		DTNHost myHost = getHost();
		DTNHost otherNode = con.getOtherNode(myHost);
		DecisionEngineRouter otherRouter = (DecisionEngineRouter)otherNode.getRouter();
		if(con.isUp())
		{
			decider.connectionUp(myHost, otherNode);
			
			/*
			 * This part is a little confusing because there's a problem we have to
			 * avoid. When a connection comes up, we're assuming here that the two 
			 * hosts who are now connected will exchange some routing information and
			 * update their own based on what the get from the peer. So host A updates
			 * its routing table with info from host B, and vice versa. In the real
			 * world, A would send its *old* routing information to B and compute new
			 * routing information later after receiving B's *old* routing information.
			 * In ONE, changedConnection() is called twice, once for each host A and
			 * B, in a serial fashion. If it's called for A first, A uses B's old info
			 * to compute its new info, but B later uses A's *new* info to compute its
			 * new info.... and this can lead to some nasty problems. 
			 * 
			 * To combat this, whichever host calls changedConnection() first calls
			 * doExchange() once. doExchange() interacts with the DecisionEngine to
			 * initiate the exchange of information, and it's assumed that this code
			 * will update the information on both peers simultaneously using the old
			 * information from both peers.
			 *
			if(shouldNotifyPeer(con))
			{
				this.doExchange(con, otherNode);
				otherRouter.didExchange(con);
			}
			
			/*
			 * Once we have new information computed for the peer, we figure out if
			 * there are any messages that should get sent to this peer.
			 *
			Collection<Message> msgs = getMessageCollection();
			for(Message m : msgs)
			{
				if(decider.shouldSendMessageToHost(m, otherNode))
					outgoingMessages.add(new Tuple<Message,Connection>(m, con));
			}
		}
		else
		{
			decider.connectionDown(myHost, otherNode);
			
			conStates.remove(con);
			
			/*
			 * If we  were trying to send message to this peer, we need to remove them
			 * from the outgoing List.
			 *
			for(Iterator<Tuple<Message,Connection>> i = outgoingMessages.iterator(); 
					i.hasNext();)
			{
				Tuple<Message, Connection> t = i.next();
				if(t.getValue() == con)
					i.remove();
			}
		}
	}*/
	
	protected void doExchange(Connection con, DTNHost otherHost)
	{
		conStates.put(con, 1);
		decider.doExchangeForNewConnection(con, otherHost);
	}
	
	/**
	 * Called by a peer DecisionEngineRouter to indicated that it already 
	 * performed an information exchange for the given connection.
	 * 
	 * @param con Connection on which the exchange was performed
	 */
	protected void didExchange(Connection con)
	{
		conStates.put(con, 1);
	}
	
	@Override
	protected int startTransfer(Message m, Connection con)
	{
		int retVal;
		
		if (!con.isReadyForTransfer()) {
			return TRY_LATER_BUSY;
		}
		
		retVal = con.startTransfer(getHost(), m);
		if (retVal == RCV_OK) { // started transfer
			addToSendingConnections(con);
		}
		else if(tombstoning && retVal == DENIED_DELIVERED)
		{
			this.deleteMessage(m.getId(), false);
			tombstones.add(m.getId());
		}
		else if (deleteDelivered && (retVal == DENIED_OLD || retVal == DENIED_DELIVERED) && 
				decider.shouldDeleteOldMessage(m, con.getOtherNode(getHost()))) {
			/* final recipient has already received the msg -> delete it */
			if(m.getId().equals("M14"))
				System.out.println("Host: " + getHost() + " told to delete M14");
			this.deleteMessage(m.getId(), false);
		}
		
		return retVal;
	}

	@Override
	public int receiveMessage(Message m, DTNHost from)
	{
		if(isDeliveredMessage(m) || (tombstoning && tombstones.contains(m.getId())))
			return DENIED_DELIVERED;
			
		return super.receiveMessage(m, from);
	}

	@Override
	public Message messageTransferred(String id, DTNHost from)
	{
		Message incoming = removeFromIncomingBuffer(id, from);
	
		if (incoming == null) {
			throw new SimError("No message with ID " + id + " in the incoming "+
					"buffer of " + getHost());
		}
		
		incoming.setReceiveTime(SimClock.getTime());
		
		Message outgoing = incoming;
		for (Application app : getApplications(incoming.getAppID())) {
			// Note that the order of applications is significant
			// since the next one gets the output of the previous.
			outgoing = app.handle(outgoing, getHost());
			if (outgoing == null) break; // Some app wanted to drop the message
		}
		
		Message aMessage = (outgoing==null)?(incoming):(outgoing);
		
		boolean isFinalRecipient = decider.isFinalDest(aMessage, getHost());
		boolean isFirstDelivery =  isFinalRecipient && 
			!isDeliveredMessage(aMessage);
		
		if (outgoing!=null && decider.shouldSaveReceivedMessage(aMessage, getHost())) 
		{
			// not the final recipient and app doesn't want to drop the message
			// -> put to buffer
			addToMessages(aMessage, false);
			
			// Determine any other connections to which to forward a message
			findConnectionsForNewMessage(aMessage, from);
		}
		
		if (isFirstDelivery)
		{
			this.deliveredMessages.put(id, aMessage);
		}
		
		for (MessageListener ml : this.mListeners) {
			ml.messageTransferred(aMessage, from, getHost(),
					isFirstDelivery);
		}
		
		return aMessage;
	}

	@Override
	protected void transferDone(Connection con)
	{
		Message transferred = this.getMessage(con.getMessage().getId());
		
		for(Iterator<Tuple<Message, Connection>> i = outgoingMessages.iterator(); 
		i.hasNext();)
		{
			Tuple<Message, Connection> t = i.next();
			if(t.getKey().getId().equals(transferred.getId()) && 
					t.getValue().equals(con))
			{
				i.remove();
				break;
			}
		}
		
		if(decider.shouldDeleteSentMessage(transferred, con.getOtherNode(getHost())))
		{
			if(transferred.getId().equals("M14"))
				System.out.println("Host: " + getHost() + " deleting M14 after transfer");
			this.deleteMessage(transferred.getId(), false);
			
			for(Iterator<Tuple<Message, Connection>> i = outgoingMessages.iterator(); 
			i.hasNext();)
			{
				Tuple<Message, Connection> t = i.next();
				if(t.getKey().getId().equals(transferred.getId()))
				{
					i.remove();
				}
			}
		}
	}

	@Override
	public void update()
	{
		super.update();
		if (!canStartTransfer() || isTransferring()) {
			return; // nothing to transfer or is currently transferring 
		}
		findConnectionsForNewMessage(); //perform a two stage replay selection
		tryMessagesForConnected(outgoingMessages);
		
		for(Iterator<Tuple<Message, Connection>> i = outgoingMessages.iterator(); 
			i.hasNext();)
		{
			Tuple<Message, Connection> t = i.next();
			if(!this.hasMessage(t.getKey().getId()))
			{
				i.remove();
			}
		}
	}
	
	public RoutingDecisionEngine getDecisionEngine()
	{
		return this.decider;
	}

	protected boolean shouldNotifyPeer(Connection con)
	{
		Integer i = conStates.get(con);
		return i == null || i < 1;
	}
	
	
	/** 
	 * Implements the two stage relay selection process
	 * @param m
	 * @param from
	 */
	protected void findConnectionsForNewMessage(Message m, DTNHost from)
	{
		/*for(Connection c : getHost()) 
		//for(Connection c : getConnections())
		{
			DTNHost other = c.getOtherNode(getHost());
			if(other != from && decider.shouldSendMessageToHost(m, other))
			{
				if(m.getId().equals("M14"))
					System.out.println("Adding attempt for M14 from: " + getHost() + " to: " + other);
				outgoingMessages.add(new Tuple<Message, Connection>(m, c));
			}
		}*/
	}
	protected void findConnectionsForNewMessage()
	{
		DTNHost thisHost = this.getHost();
		//the messages that this host is having
		Collection<Message> messages = thisHost.getMessageCollection();
		int n = messages.size(); // required for finding weight of the node
		//temporary buffer to save optimally selected data items
		Map<Connection,List<Message>> carry = new HashMap<Connection,List<Message>>();
		//compute and store the weight of each node in this list
		List<Tuple<Connection,Double>> weight = new ArrayList<Tuple<Connection,Double>>();
		for(Connection c: getHost())
		{
			DTNHost other = c.getOtherNode(thisHost);
			Collection<Message> nodeMessages  = other.getMessageCollection();
			DecisionEngineRouter d = (DecisionEngineRouter)other.getRouter();
			//have to get the path weight for all messages to pass through this node as relay
			List<Tuple<Message,Double>> pij = new ArrayList<Tuple<Message,Double>>();
			double nodeweight = 0.0; //to store the weight of this relay
			for(Message it: messages)
			{
				double cost = this.findcost(it, other);
				nodeweight+=cost;
				Tuple<Message, Double> temp = new Tuple<Message,Double>(it,cost);
				pij.add(temp);
				
			}
			pij = this.sortDec(pij);
			Iterator<Tuple<Message,Double>> it = pij.iterator();
			
			List<Message> addition = new ArrayList<Message>();
			
			while(it.hasNext())
			{
				Tuple<Message,Double> temp = it.next();
				Message curr = temp.getKey();
				int size = ((int)curr.getSize()) + 1;//a close approximatoion of the message size
				int free = d.getFreeBufferSize();
				if(size<free && !nodeMessages.contains(curr))
				{
					free -= size;
					//add message to the temporary storage assumed for the node
					addition.add(curr);
					
				}
			}
			nodeweight/=n;
			nodeweight = 1-nodeweight;
			weight.add(new Tuple<Connection,Double>(c,nodeweight));
			carry.put(c,addition);
		}
		weight = this.sortInc(weight);
		double p = 0.5; //change this as per the required delivery ration
		double q = 1;
		Iterator<Tuple<Connection,Double>> it = weight.iterator();
		while(it.hasNext() && q>1-p)
		{
			Tuple<Connection,Double> temp = it.next();
			Connection c = temp.getKey();
			double w = temp.getValue();
			q = q*w;
			List<Message> addMessage = carry.get(c);
			Iterator<Message> mes = addMessage.iterator();
			while(mes.hasNext())
			{
				Message mess = mes.next();
				Tuple<Message,Connection> tup = new Tuple<Message,Connection>(mess,c);
				if(!this.outgoingMessages.contains(tup))
					this.outgoingMessages.add(new Tuple<Message,Connection>(mess,c));
			}
		}
	}
	
	private double findcost(Message m, DTNHost h)
	{
		DecisionEngineRouter otherRouter  = (DecisionEngineRouter)h.getRouter();
		MDMDecisionEngine mdm = (MDMDecisionEngine)otherRouter.getDecisionEngine();
		int n = 0;
		double val = 0.0;
		Iterator<DTNHost> it = m.multicast_address.iterator();
		while(it.hasNext())
		{
			DTNHost node = it.next();
			double w = mdm.getPathWeightforNode(node);
			if(w==Double.MIN_VALUE)
				continue;
			n++;
			val+=w;
		}
		if(n==0)
			return Double.MIN_VALUE;
		else
			return val/n;
	}
	
	private List<Tuple<Message,Double>> sortDec(List<Tuple<Message,Double>> list)
	{
		Collections.sort(list, new Comparator<Tuple<Message,Double>>()
		{
			public int compare(Tuple<Message,Double> o1,Tuple<Message,Double> o2)
			{
				double d1 = o1.getValue();
				double d2 = o2.getValue();
				if(d1 == d2)
					return 0;
				else if(d1>d2)
					return -1;
				else
					return 1;
				
			}
		});
		return list;
	}
	
	private List<Tuple<Connection,Double>> sortInc(List<Tuple<Connection,Double>> list)
	{
		Collections.sort(list, new Comparator<Tuple<Connection,Double>>()
		{
			public int compare(Tuple<Connection,Double> o1,Tuple<Connection,Double> o2)
			{
				double d1 = o1.getValue();
				double d2 = o2.getValue();
				if(d1 == d2)
					return 0;
				else if(d1<d2)
					return -1;
				else
					return 1;
				
			}
		});
		return list;
	}
}
