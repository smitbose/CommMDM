package routing.decisionengine;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import routing.DecisionEngineRouter;
import routing.MessageRouter;
import routing.RoutingDecisionEngine;
import routing.community.CommunityDetection;
import routing.community.CommunityDetectionEngine;
import routing.community.Duration;
import routing.community.KCliqueCommunityDetection;
import core.Connection;
import core.DTNHost;
import core.Message;
import core.Settings;
import core.SimClock;

/**
 * This takes routing decisions based on Multiple Data Multicast routing scheme
 * @author soumit
 *
 */
public class MDMDecisionEngine implements RoutingDecisionEngine, CommunityDetectionEngine {
	
	public static final String COMM_ALG_SETTING = "communityDetectAlgo";
	protected CommunityDetection community;
	
	protected Map<DTNHost, Double> startTimestamp; 
	protected Map<DTNHost, List<Duration>> connHistory; //history of the connections
	
	protected Map<DTNHost, Double> pathweight; //P
	
	/**
	 * Constructor
	 */
	public MDMDecisionEngine(Settings s)
	{
		this.community = (CommunityDetection)s.createIntializedObject(s.getSetting(COMM_ALG_SETTING));
		this.startTimestamp = new HashMap<DTNHost, Double>();
		this.connHistory = new HashMap<DTNHost, List<Duration>>();
		pathweight = new HashMap<DTNHost, Double>();
	//	this.forwardingTable = new HashMap<DTNHost, List<Double>>();
	}
	
	
	/**
	 * Copy constructor
	 */
	public MDMDecisionEngine(MDMDecisionEngine proto)
	{
		this.community = proto.community.replicate();
		this.startTimestamp = new HashMap<DTNHost, Double>();
		this.connHistory = new HashMap<DTNHost, List<Duration>>();
		this.pathweight = new HashMap<DTNHost, Double>();
	//	this.forwardingTable = new HashMap<DTNHost, List<Double>>();
	}
	
	
	@Override
	public Set<DTNHost> getLocalCommunity() {
		return this.community.getLocalCommunity();
	}
	
	/*
	 * As two nodes connect with each other we update their forwardin tables
	 */
	@Override
	public void connectionUp(DTNHost thisHost, DTNHost peer) {
		exchangePathTable(thisHost,peer);
	}
	/*
	 * There is a call to community.connectionLost() where the forwardingTable will be updated
	 * So in this method, we are updating the pathweights accordingly after call to 
	 * community.connectionLost()
	 */
	@Override
	public void connectionDown(DTNHost thisHost, DTNHost peer) {
		double time = startTimestamp.get(peer);
		double etime = SimClock.getTime();
		
		// Find or create the connection history list
		List<Duration> history;
		if(!connHistory.containsKey(peer))
		{
			history = new LinkedList<Duration>();
			connHistory.put(peer, history);
		}
		else
			history = connHistory.get(peer);
		
		// add this connection to the list
		if(etime - time > 0)
			history.add(new Duration(time, etime));
		
		CommunityDetection peerCD = this.getOtherDecisionEngine(peer).community;
		
		// inform the community detection object that a connection was lost.
		// The object might need the whole connection history at this point.
		community.connectionLost(thisHost, peer, peerCD, history);
		updatePathTable();
		startTimestamp.remove(peer);
		
	}
	
	private MDMDecisionEngine getOtherDecisionEngine(DTNHost peer) {
		MessageRouter otherRouter = peer.getRouter();
		assert otherRouter instanceof DecisionEngineRouter : "This router only works " + 
		" with other routers of same type";
		
		return (MDMDecisionEngine) (((DecisionEngineRouter)otherRouter).getDecisionEngine());
	}


	@Override
	public void doExchangeForNewConnection(Connection con, DTNHost peer) {
		DTNHost myHost = con.getOtherNode(peer);
		MDMDecisionEngine de = this.getOtherDecisionEngine(peer);
		
		this.startTimestamp.put(peer, SimClock.getTime());
		de.startTimestamp.put(myHost, SimClock.getTime());
		
		this.community.newConnection(myHost, peer, de.community);
		
		updatePathTable(); 		
	}
	
	@Override
	public boolean newMessage(Message m) {
		// TODO find the possible relays for this message and tabulate
		
		return true;
	}
	
	@Override
	public boolean isFinalDest(Message m, DTNHost aHost) {
		return m.multicast_address.contains(aHost); //temporarily assuming unicast routing
		//return false;
	}
	
	@Override
	public boolean shouldSaveReceivedMessage(Message m, DTNHost thisHost) {
		//return m.getTo() != thisHost; //again assuming unicast routing
		return !(m.multicast_address.contains(thisHost));
		//return false;
	}
	
	@Override
	public boolean shouldSendMessageToHost(Message m, DTNHost otherHost) {
		// TODO Determine routing logic
		return false;
	}
	
	@Override
	public boolean shouldDeleteSentMessage(Message m, DTNHost otherHost) {
		// TODO Have to figure out the logic and details
		return false;
	}
	
	@Override
	public boolean shouldDeleteOldMessage(Message m, DTNHost hostReportingOld) {
		// TODO don't know
		return false;
	}
	
	
	@Override
	public RoutingDecisionEngine replicate() {
		return new MDMDecisionEngine(this);
	}
	
	public CommunityDetection getCommunity()
	{
		return this.community;
	}
	private void exchangePathTable(DTNHost thisHost,DTNHost peer)
	{
		DecisionEngineRouter other = (DecisionEngineRouter)peer.getRouter();
		MDMDecisionEngine otherEngine = (MDMDecisionEngine)other.getDecisionEngine();
		
		for(Map.Entry<DTNHost, Double> entry:pathweight.entrySet())
		{
			if(otherEngine.pathweight.containsKey(entry.getKey()))
			{
				if(otherEngine.pathweight.get(entry.getKey()) > pathweight.get(entry.getKey()))
				{
					DTNHost h = entry.getKey();
					pathweight.put(h, otherEngine.pathweight.get(h));
				}
			}
		}
		for(Map.Entry<DTNHost, Double> entry:otherEngine.pathweight.entrySet())
		{
			if(pathweight.containsKey(entry.getKey()))
			{
				if(otherEngine.pathweight.get(entry.getKey()) < pathweight.get(entry.getKey()))
				{
					DTNHost h = entry.getKey();
					otherEngine.pathweight.put(h, pathweight.get(h));
				}
			}
		}
	}
	/*
	 * Adding the pathweight of the nodes that have been recently added to localcommunity
	 */
	private void updatePathTable()
	{
		Set<DTNHost> localnodes = community.getLocalCommunity();
		Iterator<DTNHost> it = localnodes.iterator();
		while(it.hasNext())
		{
			DTNHost h = it.next();
			if(!pathweight.containsKey(h))
			{
				double temp = ((KCliqueCommunityDetection)community).pathweight(h);
				pathweight.put(h, temp);
			}
			
		}
	}
	
	public double getPathWeightforNode(DTNHost h)
	{
		if(this.pathweight.containsKey(h))
			return this.pathweight.get(h);
		return Double.MIN_VALUE;
	}
}
