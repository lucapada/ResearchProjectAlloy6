/**
A Software-Defined Network [5] (SDN) is a modern networking paradigm that explicitly separates the
data and control planes to include intelligence in the network. Figure 1 shows the basic SDN architec-
ture, which is composed of two main kinds of elements: (1) The Controller is the core entity of the SDN
control plane. The network intelligence is logically centralized in the controller, which is able to dynamically configure the forwarding devices of the data plane in order to achieve a specific goal. (2) Switches
are data plane components in charge of forwarding the data packets from its source to the destination. In
SDNs, each switch has a routing table that contains a set of rules defining how the different incoming
packets must be processed (forwarded, discarded, etc.). Finally, Hosts are the endpoints of the network,
they are the source and destination of the data plane traffic. Although hosts are not specific elements of
the SDN architecture, in our case study, they are part of the model.
The model of a SDN must only include the relevant information. Figure 2 shows the basic compo-
nents of the SDN model that we will implement in Section 3. For example, we abstract hosts, switches
and controllers as network nodes that contain ports to connect them with other nodes using port-to-port
(bidirectional) links. Although it is not explicitly represented in the meta-model, each switch has always
a specific link (and thus a port) that connects it with the controller. This connection is mainly used to
configure the switches. The data transmitted between nodes are called packets. There are two types of
packets: control packets include control plane information, such as new rules that must be installed in an
specific switch, or a request to know how to process a data packet. Data packets encapsulate information
that must be transmitted from one host to another. In this case, the relevant information are the source
and destination hosts, the type of data packets, and the current position in the network.
Switches contain tables with rules that specify how to route data packets. Simplifying, a rule is a
structure with a field denoting the type of data packet (e.g. HTTP or FTP) and the input and output ports.
The meaning of the rule is as follows. If a data packet of a particular type arrives at port PortI , it must be
forwarded through port PortO. In addition, it is also possible to define rules that discard incoming data
packets. When a switch has no rule to deal with a data packet, it sends a request to the controller in order
to know how to process the packet. Finally, the controller can also send new rules to switches to update
the routing tables. This description shows that a SDN has a complex static structure with nodes, links,
packages, rules and routing tables. It also has a complex dynamic behaviour when packets move through
the network nodes.
**/


sig Port {}
abstract sig Link {
	p1, p2: Port
}

sig CtrLink extends Link {}
sig DataLink extends Link {}

abstract sig DataPacketType {}
one sig TCP extends DataPacketType {}
one sig HTTP extends DataPacketType {}
abstract sig Node {
	ports: some Port,
	connected: some Node
}

sig DataPacket extends Packet {
	type: DataPacketType,
	src, dest: Host
}
sig CtrPacket extends Packet {
	newRule: lone Rule,
	request: lone DataPacket
}

abstract sig Action {}
one sig Forward extends Action {}
one sig Discard extends Action {}
sig Rule {
	packetType: DataPacketType,
	iPort: Port,
	action: Action,
	oPort: lone Port
}

one sig Controller extends Node {}


// Functions
fun node(p : Port) : Node {
	ports.p
}
fun link(p : Port) : Link {
	p1.p + p2.p
}
fun nodeLinks(n : Node) : Link {
	{ l : Link | some l.(p1 + p2) & n.ports }
}
fun reachableNodes(n : Node) : Node {
	n.^connected
}
fun dataLinks(n : Node) : Link {
	nodeLinks[n] & DataLink
}
fun remotePort(p : Port) : Port {
	(link[p].(p1 + p2)) - p
}

// Facts
fact LinksAndPorts {
	// 1 - Link ports are different
	all l : Link | l.p1 != l.p2
	// 2 - each port belongs to a node
	all p : Port | one node[p]
	// 3 - each port is at most in a link
	all p : Port | lone link[p]
	// 4 - Links connect different nodes
	all l : Link | node [l.p1]!= node[l.p2]
}

fact Links {
	// 5 - connected is well defined
	all n : Node | n.connected = { m : Node - Controller | some l : Link | node[l.(p1 + p2)] = n + m }
	// 6 - Control links connect switches and Controller
	all l : CtrLink | one node[l.(p1 + p2)] & Controller and one node[l.(p1 + p2)] & Switch
	// 7 - Data links connect two switches or a switch and a host
	all l : DataLink | some node[l.(p1 + p2)] & Switch and Controller not in node[l.(p1 + p2)]
	// 8 - all controller links are control links
	nodeLinks[Controller] in CtrLink
	// 9 - the controller has exactly a link to each switch
	all s : Switch | one nodeLinks[Controller] & nodeLinks[s]
	// 10 - switches have at least two data links
	all s : Switch | #nodeLinks[s] & DataLink >=2
}

fact Nodes {
	// 11 - switches can at least reach two hosts
	all s : Switch | #(reachableNodes[s] & Host) >=2
	// 12 - switches have at least two nodes connected
	all s : Switch | #s.connected >=2
	// 13 - Hosts do not have links to the Controller
	no nodeLinks [Controller] & nodeLinks[Host]
	// 14 - Each host has only one link to a switch
	all h : Host | one s : Switch | h.connected = s
}

fact DataPackets {
	// 15 - at most one packet in a port
	all p : Port | lone position.p
	// 16 - data packets are well placed at ports or buffer hosts
	all packet : DataPacket | one packet.position or one (iBuffer + oBuffer).packet
}

fact DataControlLinks {
	// 17 - A data link contains only DataPackets
	all l : DataLink | l.(p1 + p2)[position] in DataPacket
	// 18 - A control link c o n t a i n s only CtrPackets
	all l : CtrLink | l.(p1 + p2)[position] in CtrPacket
}

fact Packets {
	// 19 - The source and destination hosts of a DataPacket are different
	all pack : DataPacket | pack.src != pack.dest
	// 20 - Each control packet has a new rule or a request
	all pack : CtrPacket | one pack.(newRule + request)
	// 21 - A control packet with a new rule arrives to a Switch port
	all pack : CtrPacket | (one pack.position & Switch.ports) implies one pack.newRule
	// 22 - A control packet with a request arrives to a Controller port
	all pack : CtrPacket | (one pack.position & Controller.ports) implies one pack.request
	// 23 - iBuffer is well defined
	all h : Host | h.iBuffer in { pack : DataPacket | (no pack.position) and pack.dest = h }
	// 24 - oBuffer is well defined
	all h : Host | h.oBuffer in { pack : DataPacket | (no pack.position) and pack.src = h }
	// 25 - Packets in an oBuffer can reach the destination host
	all h : Host, pack : h.iBuffer | pack.dest in reachableNodes[h]
}

fact RulesAndTables {
	// 26 - Each rule belongs to a table at most
	all r : Rule | lone table.r
	// 27 - Each switch has at most one rule for each data type and input port
	all s : Switch, disj r1, r2 : s.table | r1.packetType != r2.packetType or r1.iPort != r2.iPort
	// 28 - The input port of a rule belongs to a switch and a data link
	all r : Rule | one(r.iPort & Switch.ports) and one (r.iPort & dataLinks[Switch].(p1 + p2))
	// 29 - Forward rules have output port
	all r : Rule | one r.oPort iff r.action = Forward and one(r.oPort & dataLinks[Switch].(p1 + p2))
	// 30 - Discard rules have no output port
	all r : Rule | # r.oPort = 0 iff r.action = Discard
	// 31 - The input and output ports of a rule are different
	all r : Rule | r.iPort != r.oPort
	// 32 - The iPort and oPort of a rule in a switch belong to the switch
	all s : Switch, r : s.table | node[r.(iPort + oPort)] = s
}

/** DYNAMIS ISTANCES: given a packet on switch port, the model does not specify how the packet position changes to reach the destination host. 
The goal of this section is to transform static ALLOY models into dynamic ones.**/

/** The introduction of the mutable keyword "var" makes possible to have an evolution of Packets, Routing Table and Buffering Queues of each Node over time. **/
abstract sig Packet {
	var position: lone Port
}

sig Host extends Node {
	var iBuffer: set DataPacket,
	var oBuffer: set DataPacket
}
sig Switch extends Node {
	var table: set Rule
}

fact TimeFacts {
	// 15 - at most one packet in a port
	// all t : Time, p : Port | lone (position.t).p
	always all p: Port | lone position.p
	// 16 - data packets are well placed at ports or buffer hosts
	// all t : Time, pk : DataPacket | (one pk.position.t) or (one(iBuffer + oBuffer).t.pk)
	always all pk: DataPacket | one(pk.position) or one(iBuffer + oBuffer).pk
	// 17 - DataLink contains only DataPackets
	//all t : Time, l : DataLink | l.(p1 + p2)[position.t] in DataPacket
	always all l: DataLink | l.(p1 + p2)[position] in DataPacket
	// 18 - A control link contains only control packets
	// all t : Time, l : CtrLink | l.(p1 + p2)[position.t] in CtrPacket
	always all l: CtrLink | l.(p1 + p2)[position] in CtrPacket
	// 21 - A control packet with a new rule arrives to a Switch port
	// all t : Time, pk : CtrPacket | (one pk.position.t & Switch.ports) implies one pk.newRule
	always all pk: CtrPacket | (one pk.position & Switch.ports) implies one pk.newRule
	// 22 - A control packet with a request arrives to a Controller port
	// all t : Time, pk : CtrPacket |
	//	(one pk.position.t & Controller.ports) implies one pk.request
	always all pk: CtrPacket |
		(one pk.position & Controller.ports) implies one pk.request
	// 23 - iBuffer is well defined
	// all t : Time, h : Host |
	//	h.iBuffer.t in { pk : DataPacket | (no pk.position.t) and pk.dest = h }
	always all h: Host |
		h.iBuffer in { pk: DataPacket | (no pk.position) and pk.dest = h }
	// 24 - oBuffer is well defined
	// all t : Time, h : Host |
	//	h.oBuffer.t in { pk : DataPacket | (no pk.position.t) and pk . src = h }
	always all h: Host |
		h.oBuffer in { pk: DataPacket | (no pk.position) and pk.src = h }
	// 25 - Packets in an iBuffer can reach the destination host
	// all t : Time, h : Host, pk : h.iBuffer.t | pk.dest in reachableNodes[h]
	always all h: Host, pk: h.iBuffer | pk.dest in reachableNodes[h]
	// 26 - Each rule belongs to a table at most
	// all t : Time, r : Rule | lone table.t.r
	always all r: Rule | lone table.r
	// 27 - Each switch has at most one rule for each data type and input port
	// all t : Time, s : Switch, disj r1, r2 : s.table.t |
	//	r1.packetType != r2.packetType or r1.iPort != r2.iPort
	always all s: Switch, disj r1, r2 : s.table |
		r1.packetType != r2.packetType or r1.iPort != r2.iPort
	// 32 - The iPort and oPort of rules of a switch have to be different ports of the switch
	// all t : Time, s : Switch, r : s.table.t | node[r.(iPort + oPort)] = s
	always all s: Switch, r: s.table | node[r.(iPort + oPort)] = s
}

pred allPacketsUnmodifiedExcept(pp: set Packet) {
	always all pk: Packet - pp | pk.position = pk.position'
}
pred alloBuffersUnmodifiedExcept(hh: set Host) {
	always all h: Host - hh | h.oBuffer = h.oBuffer'
}
pred alliBuffersUnmodifiedExcept(hh: set Host) {
	always all h: Host - hh | h.iBuffer = h.iBuffer'
}
pred allTablesUnmodifiedExcept(ss: set Switch) {
	always all s: Switch - ss | s.table = s.table'
}

pred installRule(s: Switch, pk: CtrPacket){}
pred sendRequest(s: Switch, pk: DataPacket){}
pred receiveRequest(ctrl: Controller, req: CtrPacket){}

pred discardPacket(s: Switch, pk: DataPacket) {
	// pre
	always some pk.position & s.ports and some r : s.table | r.action = Discard and r.iPort = pk.position and r.packetType = pk.type
	implies after pk.position = none
	// frame
	allTablesUnmodifiedExcept[none]
	allPacketsUnmodifiedExcept[pk]
	alloBuffersUnmodifiedExcept[none]
	alliBuffersUnmodifiedExcept[none]
}

pred forwardPacket(s: Switch, pk: DataPacket) {
	// pre
	always some pk.position & s.ports and some r : s.table | (r.packetType = pk.type and r.action = Forward and r.iPort = pk.position) 
	implies {
		// post
		let r = s.table & packetType.(pk.type) & action.Forward & iPort.(pk.position), p = remotePort[r.oPort] | after pk.position = p
		// frame
		allTablesUnmodifiedExcept[none] and allPacketsUnmodifiedExcept[pk]
		alloBuffersUnmodifiedExcept[none]
		alliBuffersUnmodifiedExcept[none]
	}
}

pred sendPacket(h: Host, pk: DataPacket) {
	// pre
	always some pk & h.oBuffer
	implies
	// post
	some p: remotePort[h.ports] | after (pk.position = p and h.oBuffer = h.oBuffer - pk)
	// frame
	allTablesUnmodifiedExcept[none]
	allPacketsUnmodifiedExcept[pk]
	alloBuffersUnmodifiedExcept[h]
	alliBuffersUnmodifiedExcept[none]
}

pred receivePacket(h: Host, pk: DataPacket) {
	// pre
	always some (pk.position & h.ports)
	// post
	implies after (h.iBuffer = h.iBuffer + pk and pk.position = none)
	// frame
	allTablesUnmodifiedExcept[none]
	allPacketsUnmodifiedExcept[pk]
	alloBuffersUnmodifiedExcept[none]
	alliBuffersUnmodifiedExcept[h]
}

// OK
/*pred Config1(){
	#Controller = 1 and #Host = 2 and #Switch >=2 and #DataPacket = 2
	// all ports are in a link
	all p: Port | one link[p]
	// all rules are different in the system/topology
	no disj r1, r2 : Rule | r1.iPort = r2.iPort and r1.oPort = r2.oPort
	and r1.action = r2.action and r1.packetType = r2.packetType
}
run Config1 for 10*/

pred initTopology3() {
	#Controller = 1 and #Host = 2 and #Switch >=2 and #DataPacket = 2
	
	// all DataPackets are initially in the oBuffers of the hosts
	always all pk: DataPacket | pk in Host.oBuffer
	// No CtrPackets in switches or controller ports in T0
	always all pk: CtrPacket | pk.position = none
	// all ports are in a link
	all p: Port | one link[p]
	// all switches has some pre-installed rules
	all s: Switch | some s.table
	// all forwarding rules are pre-installed
	all r: Rule | r.action = Forward implies r in Switch.table
	// all rules are different in the system
	no disj r1, r2: Rule | r1.iPort = r2.iPort and r1.oPort = r2.oPort and (r1.action = r2.action) and (r1.packetType = r2.packetType)
}

// OK
pred Config3(){ 
	always (some h: Host, s: Switch, pk: DataPacket, ctrl: Controller, ctrPk: CtrPacket | historically (
		initTopology3[] and
		sendPacket[h, pk] or receivePacket[h, pk] or
		forwardPacket[s, pk] or discardPacket[s, pk] or
		installRule[s, ctrPk] or sendRequest[s, pk] or
		receiveRequest[ctrl, ctrPk]
	))
}
// run Config3 for 10 /*but 9 Time*/


// Controller does not receive requests: assertion invalid...
assert noRequest { 
	Config3 implies no pk: CtrPacket |
	always one (pk.position & Controller.ports)
}
// check noRequest for 10 /*but 9 Time*/

// non sono sicuro di queste ultime due...

// all data packets arrive to the destination host: assertion invalid...
assert packetArrival { 
	Config3 implies (always all pk : DataPacket |
		(one pk & pk.src.oBuffer) and eventually(one pk & pk.dest.iBuffer)) 
}
// check packetArrival for 10 /*but 9 Time*/

// Search for instances with more than 5 Hosts
assert Hosts5 { Config3 implies #Host < 5 }
check Hosts5 for 15
