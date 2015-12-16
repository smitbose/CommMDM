/*
 * @(#)KCLiqueCommunityDetection.java
 *
 * Copyright 2010 by University of Pittsburgh, released under GPLv3.
 */
package routing.community;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import routing.DecisionEngineRouter;
import routing.MessageRouter;
import routing.decisionengine.MDMDecisionEngine;
import core.DTNHost;
import core.Settings;

/**
 * <p>Performs the K-Clique Community Detection algorithm described in 
 * <em>Distributed Community Detection in Delay Tolerant Networks</em> by Pan
 * Hui et al. (bibtex record is included below for convenience). A node using
 * K-Clique keeps a record of all the nodes it has met and the cummulative 
 * contact duration it has had with each. Once this total contact duration for 
 * one of these nodes exceeds a configurable parameter, the node is added to the 
 * host's familiar set and local community and the node's familiar set is added 
 * to an approximation of all the familiar sets of the host's local community.  
 * </p>
 * <p>Note: In ONE, each KCliqueCommunityDetection stores a reference to another 
 * node's familiar set instead of creating and managing a duplicate of it. 
 * </p>
 * <p>When two peers meet, they exchange familiar sets, local community sets, 
 * and their respective approximations of the familiar sets of their local 
 * communities. If the nodes are not part of each other's local communities, 
 * the set intersection between the local community of one host and the familiar
 * set of its peer is computed. If the size of this intersection is 
 * greater than the configurable parameter, <code>K</code>, the peer has K nodes
 * in common with the local community and should therefore be added to the local
 * community. In this case, then, the peer's local community may have other 
 * nodes that also share K nodes in common with the local community, which then
 * should be added to it as well. 
 * </p>
 * <pre>
 * \@inproceedings{1366929,
 * Address = {New York, NY, USA},
 * Author = {Hui, Pan and Yoneki, Eiko and Chan, Shu Yan and Crowcroft, Jon},
 * Booktitle = {MobiArch '07: Proceedings of 2nd ACM/IEEE international workshop 
 * 	on Mobility in the evolving internet architecture},
 * Doi = {http://doi.acm.org/10.1145/1366919.1366929},
 * Isbn = {978-1-59593-784-8},
 * Location = {Kyoto, Japan},
 * Pages = {1--8},
 * Publisher = {ACM},
 * Title = {Distributed Community Detection in Delay Tolerant Networks},
 * Year = {2007}
 * }
 * </pre>
 * 
 * @author PJ Dillon, University of Pittsburgh
 */
public class KCliqueCommunityDetection implements CommunityDetection
{
	public static final String K_SETTING = "K";
	public static final String FAMILIAR_SETTING = "familiarThreshold";
	
	protected Set<DTNHost> familiarSet; //F0
	protected Set<DTNHost> localCommunity; //C0
	protected Map<DTNHost, Set<DTNHost>> familiarsOfMyCommunity; //FS0LC0
	protected Map<DTNHost, List<Double>> forwardingTable; //social forwarding path table
	protected Map<DTNHost, Double> lambda; //edge weights
	
	
	protected double k;
	protected double familiarThreshold;
	
	private double T; //time constraint
	
	public KCliqueCommunityDetection(Settings s)
	{
		this.k = s.getDouble(K_SETTING);
		this.familiarThreshold = s.getDouble(FAMILIAR_SETTING);
		this.T = MessageRouter.msgTtl;
	}
	
	public KCliqueCommunityDetection(KCliqueCommunityDetection proto)
	{
		this.k = proto.k;
		this.T = MessageRouter.msgTtl;
		this.familiarThreshold = proto.familiarThreshold;
		familiarSet = new HashSet<DTNHost>();
		localCommunity = new HashSet<DTNHost>();
		this.familiarsOfMyCommunity = new HashMap<DTNHost, Set<DTNHost>>();
		this.lambda = new HashMap<DTNHost, Double>();
		this.forwardingTable = new HashMap<DTNHost, List<Double>>();
	}
	
	public void newConnection(DTNHost myHost, DTNHost peer, 
			CommunityDetection peerCD)
	{
		KCliqueCommunityDetection scd = (KCliqueCommunityDetection)peerCD;
		
		// Ensure each node is in its own local community
		// (This is the first instance where we actually get the host for these 
		// objects)
		this.localCommunity.add(myHost);
		scd.localCommunity.add(peer);
		
		/*
		 * The first few steps of the protocol are
		 *  (1) update my local approximation of my peer's familiar set
		 *  (2) merge my and my peer's local approximations of our respective
		 *      community's familiar sets
		 * 
		 * In both these cases, for ONE, each CommunityDetection object stores a 
		 * reference to the familiar set of its community members. As those members
		 * update their familiar set, others storing a reference to that set
		 * immediately witness the reflected changes. Therefore, we don't have to 
		 * anything to update an "approximation" of the familiar sets. They're not
		 * approximations here anymore. In this way, what we have in the k-Clique
		 * community detection class is an upper bound on the performance of the
		 * protocol.
		 */
		
		// Add peer to my local community if needed
		if(!this.localCommunity.contains(peer))
		{
			/*
			 * 
			 */
			
			// compute the intersection size
			int count=0;
			DTNHost intermediate = null; //the node through which effective hop to the added node will be made
			double maxpathweight = Double.MIN_VALUE;
			List<Double> hops;
			for(DTNHost h : scd.familiarSet)
				if(this.localCommunity.contains(h))
				{
					hops = forwardingTable.get(h);
					hops.add(scd.lambda.get(h));
					double temp = pathweight(hops);
					if(temp>maxpathweight)
					{
						maxpathweight = temp;
						intermediate = h;
					}
					count++;
				}
			
			// if peer familiar has K nodes in common with this host's local community
			
			if(count >= this.k - 1)
			{
				this.localCommunity.add(peer);
				hops = forwardingTable.get(intermediate);
				hops.add(scd.lambda.get(intermediate));
				forwardingTable.put(peer, hops);
				this.familiarsOfMyCommunity.put(peer, scd.familiarSet);
				
				// search the peer's local community for other nodes with K in common
				// (like a transitivity property)
				for(DTNHost h : scd.localCommunity)
				{
					if(h == myHost || h == peer) continue;
					
					// compute intersection size
					DecisionEngineRouter hroute = (DecisionEngineRouter)h.getRouter();
					KCliqueCommunityDetection hcomm = 
							(KCliqueCommunityDetection)(((MDMDecisionEngine)hroute.getDecisionEngine()).getCommunity());
					count = 0;
					maxpathweight = Double.MIN_VALUE;
					intermediate = null;
					for(DTNHost i : scd.familiarsOfMyCommunity.get(h))
						if(this.localCommunity.contains(i))
						{
							count++;
							hops = forwardingTable.get(i);
							hops.add(hcomm.lambda.get(i));
							double temp = pathweight(hops);
							if(maxpathweight<temp)
							{
								intermediate = i;
								maxpathweight = temp;
							}
						}
					
					// add nodes if there are K in common with this local community
					if(count >= this.k - 1)
					{
						this.localCommunity.add(h);
						this.familiarsOfMyCommunity.put(h, 
								scd.familiarsOfMyCommunity.get(h));
						hops = forwardingTable.get(intermediate);
						hops.add(hcomm.lambda.get(intermediate));
						forwardingTable.put(h,hops);
					}
				}
			}
		}
		//TODO find hops from this
		// Repeat process from peer's perspective
		if(!scd.localCommunity.contains(myHost))
		{
			int count = 0;
			DTNHost intermediate = null;
			double maxpathweight = Double.MIN_VALUE;
			List<Double> hops;
			for(DTNHost h : this.familiarSet)
				if(scd.localCommunity.contains(h))
				{
					count++;
					hops = scd.forwardingTable.get(h);
					hops.add(this.lambda.get(h));
					double temp = pathweight(hops);
					if(temp>maxpathweight)
					{
						maxpathweight = temp;
						intermediate = h;
					}
				}
			if(count >= scd.k - 1)
			{
				scd.localCommunity.add(myHost);
				scd.familiarsOfMyCommunity.put(myHost, this.familiarSet);
				hops = scd.forwardingTable.get(intermediate);
				hops.add(this.lambda.get(intermediate));
				scd.forwardingTable.put(peer, hops);
				
				for(DTNHost h : this.localCommunity)
				{
					if(h == myHost || h == peer) continue;
					DecisionEngineRouter hroute = (DecisionEngineRouter)h.getRouter();
					KCliqueCommunityDetection hcomm = 
							(KCliqueCommunityDetection)(((MDMDecisionEngine)hroute.getDecisionEngine()).getCommunity());
					maxpathweight = Double.MIN_VALUE;
					intermediate = null;
					
					count = 0;
					for(DTNHost i : this.familiarsOfMyCommunity.get(h))
						if(scd.localCommunity.contains(i))
						{
							count++;
							hops = scd.forwardingTable.get(i);
							hops.add(hcomm.lambda.get(i));
							double temp = pathweight(hops);
							if(maxpathweight<temp)
							{
								intermediate = i;
								maxpathweight = temp;
							}
						}
					if(count >= scd.k - 1)
					{
						scd.localCommunity.add(h);
						scd.familiarsOfMyCommunity.put(h, 
								this.familiarsOfMyCommunity.get(h));
						hops = scd.forwardingTable.get(intermediate);
						hops.add(hcomm.lambda.get(intermediate));
						scd.forwardingTable.put(h,hops);
					}
				}
			}
		}
	}
	/*This function is responsible for adding nodes to familiar set. So we have to maintain
	 * weights here. But there is one little problem. The edge weights are contact duration and
	 * once a node is added to the familiar set, they may further meet. So do we update the
	 * edge weight or let it remain as it is?
	 */
	public void connectionLost(DTNHost myHost, DTNHost peer, 
			CommunityDetection peerCD, List<Duration> history)
	{
		if(this.familiarSet.contains(peer)) return;
		
		// Compute cummulative contact duration with this peer
		Iterator<Duration> i = history.iterator();
		double time = 0;
		while(i.hasNext())
		{
			Duration d = i.next();
			time += d.end - d.start;
		}
		
		// If cummulative duration is greater than threshold, add
		if(time > this.familiarThreshold)
		{
			KCliqueCommunityDetection scd = (KCliqueCommunityDetection)peerCD;
			this.familiarSet.add(peer);
			this.localCommunity.add(peer);
			this.familiarsOfMyCommunity.put(peer, scd.familiarSet);
			lambda.put(peer, time); //considering edge weight as the contact duration
			List<Double> hops = new ArrayList<Double>();
			hops.add(time);
			forwardingTable.put(peer, hops);
			/*here we have to add to the forwardin table also as "peer" is also added to the
			 * local community at the same time 
			 */
			
		}
	}

	public boolean isHostInCommunity(DTNHost h)
	{
		return this.localCommunity.contains(h);
	}

	public CommunityDetection replicate()
	{
		return new KCliqueCommunityDetection(this);
	}

	public Set<DTNHost> getLocalCommunity()
	{
		return this.localCommunity;
	}
	/* my implementation
	 * 
	 */
	public double pathweight(DTNHost h)
	{
		List<Double> hops = forwardingTable.get(h);
		int size = hops.size();
		double pathweight = 0.0;
		for(int i =0;i<size;i++)
		{
			double ci = getCi(hops,i);
			double temp = (1 - Math.exp((-1)*hops.get(i)*this.T)); //TODO set T
			pathweight += (ci*temp);
		}
		return pathweight;
	}
	private double pathweight(List<Double> hops)
	{
		int size = hops.size();
		double pathweight = 0.0;
		for(int i =0;i<size;i++)
		{
			double ci = getCi(hops,i);
			double temp = (1 - Math.exp((-1)*hops.get(i)*this.T)); //TODO set T
			pathweight += (ci*temp);
		}
		return pathweight;
	}
	double getCi(List<Double> hops,int i)
	{
		int size = hops.size();
		double c = 1;
		for(int j=0;j<size;j++)
		{
			if(j==i)
				continue;
			double den = hops.get(j) - hops.get(i);
			double temp = hops.get(j)/den;
			c*=temp;
		}
		return c;
	}
	public Map<DTNHost, List<Double>> getForwardingTable()
	{
		return this.forwardingTable;
	}
}
