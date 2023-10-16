-------------------------------- MODULE Traceetcdraft -------------------------------
EXTENDS etcdraft, Json, IOUtils, Sequences

\* raft.pb.go enum MessageType
RaftMsgType ==
    "MsgApp" :> AppendEntriesRequest @@ "MsgAppResp" :> AppendEntriesResponse @@
    "MsgVote" :> RequestVoteRequest @@ "MsgVoteResp" :> RequestVoteResponse

LeadershipState ==
    Leader :> "StateLeader" @@ Follower :> "StateFollower" @@ Candidate :> "StateCandidate"

-------------------------------------------------------------------------------------

\* Trace validation has been designed for TLC running in default model-checking
 \* mode, i.e., breadth-first search.
ASSUME TLCGet("config").mode = "bfs"

JsonFile ==
    IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "./example.ndjson"

TraceLog ==
    \* Deserialize the System log as a sequence of records from the log file.
     \* Run TLC with (assuming a suitable "tlc" shell alias):
     \* $ JSON=../tests/raft_scenarios/4582.ndjson tlc -note Traceccfraft
     \* Fall back to trace.ndjson if the JSON environment variable is not set.
    SelectSeq(ndJsonDeserialize(JsonFile), LAMBDA l: "tag" \in DOMAIN l /\ l.tag = "raft_trace")


ASSUME PrintT(<< "Trace:", JsonFile, "Length:", Len(TraceLog)>>)

TraceServer == { TraceLog[i].event.nid: i \in DOMAIN TraceLog }
        
TraceFirstActionLogIndex ==
    FoldSeq(LAMBDA x, y: [y EXCEPT ![TraceLog[x].event.nid] = IF @ = 0 /\ TraceLog[x].event.name # "ApplyConfChange" THEN x ELSE @], [ i \in TraceServer |-> 0], [j \in DOMAIN TraceLog |-> j])

ASSUME \A k \in DOMAIN TraceLog: k < TraceFirstActionLogIndex[TraceLog[k].event.nid] => TraceLog[k].event.state.term = 1 /\ TraceLog[k].event.state.vote = 0 /\ TraceLog[k].event.name = "ApplyConfChange"


TraceInitServer == ToSet(TraceLog[1].event.conf[1])
ASSUME TraceInitServer \subseteq TraceServer

-------------------------------------------------------------------------------------
ConfFromLog(l) == << ToSet(l.event.conf[1]), ToSet(l.event.conf[2]) >>
   
TraceInitConfVars == 
    /\ pendingConfChangeIndex = [i \in Server |-> 0]
    /\ config = [ i \in Server |-> ConfFromLog(TraceLog[TraceFirstActionLogIndex[i]]) ]

TraceInitLogVars == /\ log = [i \in Server |-> [j \in 1..TraceLog[TraceFirstActionLogIndex[i]].event.state.commit |-> [term  |-> 1, type  |-> ConfigEntry]]]
                    /\ commitIndex  = [i \in Server |-> TraceLog[TraceFirstActionLogIndex[i]].event.state.commit]

OneMoreMessage(msg) ==
    \/ msg \notin DOMAIN messages /\ msg \in DOMAIN messages' /\ messages'[msg] = 1
    \/ msg \in DOMAIN messages /\ messages'[msg] = messages[msg] + 1

OneLessMessage(msg) ==
    \/ msg \in DOMAIN messages /\ messages[msg] = 1 /\ msg \notin DOMAIN messages'
    \/ msg \in DOMAIN messages /\ messages'[msg] = messages[msg] - 1

-------------------------------------------------------------------------------------

VARIABLE l, logline

NextLogIndex(x) == IF x < Len(TraceLog) 
                        THEN CHOOSE k \in (x+1)..Len(TraceLog): k >= TraceFirstActionLogIndex[TraceLog[k].event.nid] 
                        ELSE x+1

TraceInit ==
    /\ l = NextLogIndex(0)
    /\ logline = TraceLog[l]
    /\ Init

StepToNextTrace == 
    /\ l' = IF l+1>Len(TraceLog) THEN l+1 ELSE NextLogIndex(l)
    /\ logline' = IF l' <= Len(TraceLog) THEN TraceLog[l'] ELSE {}

StepToNextTraceIfMessageIsProcessed(msg) ==
    IF OneLessMessage(msg) 
        THEN StepToNextTrace 
        ELSE UNCHANGED <<l, logline>>

-------------------------------------------------------------------------------------


LoglineIsEvent(e) ==
    \* Equals FALSE if we get past the end of the log, causing model checking to stop.
    /\ l \in 1..Len(TraceLog)
    /\ logline.event.name = e

LoglineIsMessageEvent(e, i, j) ==
    /\ LoglineIsEvent(e)
    /\ logline.event.msg.from = i
    /\ logline.event.msg.to = j

LoglineIsNodeEvent(e, i) ==
    /\ LoglineIsEvent(e)
    /\ logline.event.nid = i

LoglineIsAppendEntriesRequest(m) ==
    /\ m.mtype = AppendEntriesRequest
    /\ m.mtype = RaftMsgType[logline.event.msg.type]
    /\ m.mdest   = logline.event.msg.to
    /\ m.msource = logline.event.msg.from
    /\ m.mterm = logline.event.msg.term
    /\ m.mcommitIndex = logline.event.msg.commit
    /\ m.mprevLogTerm = logline.event.msg.logTerm
    /\ m.mprevLogIndex = logline.event.msg.index
    /\ Len(m.mentries) = logline.event.msg.entries

LoglineIsAppendEntriesResponse(m) ==
    /\ m.mtype = AppendEntriesResponse
    /\ m.mtype = RaftMsgType[logline.event.msg.type]
    /\ m.mdest   = logline.event.msg.to
    /\ m.msource = logline.event.msg.from
    /\ m.mterm = logline.event.msg.term
    /\ m.msuccess = ~logline.event.msg.reject
    /\ m.mmatchIndex = IF logline.event.msg.reject THEN logline.event.msg.rejectHint ELSE logline.event.msg.index

LoglineIsRequestVoteRequest(m) ==  
    /\ m.mtype = RequestVoteRequest
    /\ m.mtype = RaftMsgType[logline.event.msg.type]
    /\ m.mdest = logline.event.msg.to
    /\ m.msource = logline.event.msg.from
    /\ m.mterm = logline.event.msg.term
    /\ m.mlastLogIndex = logline.event.msg.index
    /\ m.mlastLogTerm = logline.event.msg.logTerm

LoglineIsRequestVoteResponse(m) ==  
    /\ m.mtype = RequestVoteResponse
    /\ m.mtype = RaftMsgType[logline.event.msg.type]
    /\ m.mdest = logline.event.msg.to
    /\ m.msource = logline.event.msg.from
    /\ m.mterm = logline.event.msg.term
    /\ m.mvoteGranted = ~logline.event.msg.reject

\* perform RequestVote transition if logline indicates so
ValidateAfterRequestVote(i, j) == 
    /\ \E m \in DOMAIN messages':
       /\ \/ LoglineIsRequestVoteRequest(m)
          \/ /\ LoglineIsRequestVoteResponse(m)
             /\ m.msource = m.mdest
       /\ OneMoreMessage(m)

RequestVoteIfLogged(i, j) ==
    /\ \/ /\ LoglineIsMessageEvent("SendRequestVoteRequest", i, j)
          /\ PrintT(<<"SendRequestVoteRequest", "from:", i, "to:", j>>)
       \* etcd candidate sends MsgVoteResp to itself upon compain starting
       \/ /\ LoglineIsMessageEvent("SendRequestVoteResponse", i, j)
          /\ i = j 
          /\ PrintT(<<"SendRequestVoteResponse", "from:", i, "to:", j>>)
    /\ RequestVote(i, j)
    /\ ValidateAfterRequestVote(i, j)
    /\ StepToNextTrace

\* perform BecomeLeader transition if logline indicates so
ValidateAfterBecomeLeader(i) == 
    /\ logline.event.role = "StateLeader"
    /\ state'[i] = Leader

BecomeLeaderIfLogged(i) ==
    /\ LoglineIsNodeEvent("BecomeLeader", i)
    /\ BecomeLeader(i)
    /\ ValidateAfterBecomeLeader(i)
    /\ StepToNextTrace

\* perform ClientRequest transition if logline indicates so
ClientRequestIfLogged(i, v) == 
    /\ LoglineIsNodeEvent("Replicate", i)
    /\ ClientRequest(i, v)
    /\ StepToNextTrace

\* perform AdvanceCommitIndex transition if logline indicates so
ValidateAfterAdvanceCommitIndex(i) ==
    /\ logline.event.role = "StateLeader"
    /\ state[i] = Leader
    /\ commitIndex'[i] >= logline.event.state.commit

AdvanceCommitIndexIfLogged(i) ==
    /\ LoglineIsNodeEvent("Commit", i)
    /\ AdvanceCommitIndex(i)
    /\ ValidateAfterAdvanceCommitIndex(i)    
    /\ StepToNextTrace

\* perform AppendEntries transition if logline indicates so
ValidateAfterAppendEntries(i, j) ==
    /\ \E msg \in DOMAIN messages':
        /\ \/ LoglineIsAppendEntriesRequest(msg)
           \/ /\ LoglineIsAppendEntriesResponse(msg)
              /\ msg.msource = msg.mdest
        \* There is now one more message of this type.
        /\ OneMoreMessage(msg)

TraceEntriesToAppend == logline.event.msg.entries

AppendEntriesIfLogged(i, j) == 
    /\ \/ /\ LoglineIsMessageEvent("SendAppendEntriesRequest", i, j)
          /\ PrintT(<<"SendAppendEntriesRequest", "from:", i, "to:", j>>)
       \* etcd leader sends MsgAppResp to itself after appending log entry
       \/ /\ LoglineIsMessageEvent("SendAppendEntriesResponse", i, j)
          /\ i = j
          /\ PrintT(<<"SendAppendEntriesResponse", "from:", i, "to:", j>>)
    /\ AppendEntries(i, j)
    /\ ValidateAfterAppendEntries(i, j)
    /\ StepToNextTrace

\* perform Receive transition if logline indicates so
LoglineIsReceivedMessage(m) ==
    \/ /\ LoglineIsEvent("ReceiveAppendEntriesRequest")
       /\ LoglineIsAppendEntriesRequest(m)
       /\ PrintT(<<"ReceiveAppendEntriesRequest", "from:", m.msource, "to:", m.mdest>>)
    \/ /\ LoglineIsEvent("ReceiveAppendEntriesResponse")
       /\ LoglineIsAppendEntriesResponse(m)
       /\ PrintT(<<"ReceiveAppendEntriesResponse", "from:", m.msource, "to:", m.mdest>>)
    \/ /\ LoglineIsEvent("ReceiveRequestVoteRequest")
       /\ LoglineIsRequestVoteRequest(m) 
       /\ PrintT(<<"ReceiveRequestVoteRequest", "from:", m.msource, "to:", m.mdest>>)
    \/ /\ LoglineIsEvent("ReceiveRequestVoteResponse")
       /\ LoglineIsRequestVoteResponse(m)
       /\ PrintT(<<"ReceiveRequestVoteResponse", "from:", m.msource, "to:", m.mdest, "grant:", m.mvoteGranted>>)

TraceNextIndexForUnsuccessfulAppendResponse(m) == logline.event.msg.index

ReceiveIfLogged(m) == 
    /\ LoglineIsReceivedMessage(m)
    /\ Receive(m)
    /\ StepToNextTraceIfMessageIsProcessed(m)

\* perform Timeout transition if logline indicates so
ValidateAfterTimeout(i) == 
    /\ logline.event.role = "StateCandidate"
    /\ logline.event.nid = i
    /\ state'[i] = Candidate
    /\ currentTerm'[i] = logline.event.state.term

TimeoutIfLogged(i) ==
    /\ LoglineIsNodeEvent("BecomeCandidate", i)
    /\ Timeout(i)
    /\ ValidateAfterTimeout(i)    
    /\ StepToNextTrace
    /\ PrintT(<<"BecomeCandidate", "node:", i>>)

\* perform AddNewServer transition if logline indicates so
AddNewServerIfLogged(i, j) ==
    /\ LoglineIsNodeEvent("ChangeConf", i)
    /\ Len(logline.event.cc.changes) = 1
    /\ logline.event.cc.changes[1].action = "AddNewServer"
    /\ logline.event.cc.changes[1].nid = j
    /\ AddNewServer(i, j)
    /\ StepToNextTrace
    /\ PrintT(<<"ChangeConf", "node:", i, "new:", j>>)

\* perform DeleteServer transition if logline indicates so
DeleteServerIfLogged(i, j) ==
    /\ LoglineIsNodeEvent("ChangeConf", i)
    /\ Len(logline.event.cc.changes) = 1
    /\ logline.event.cc.changes[1].action = "RemoveServer"
    /\ logline.event.cc.changes[1].nid = j
    /\ DeleteServer(i, j)
    /\ StepToNextTrace
    /\ PrintT(<<"ChangeConf", "node:", i, "delete:", j>>)

\* perform ApplyConfChange transition if logline indicates so
ApplyConfChangeIfLogged(i) ==
    /\ LoglineIsNodeEvent("ApplyConfChange", i)
    /\ ApplyConfChange(i)
    /\ StepToNextTrace
    /\ PrintT(<<"ApplyConfChange", "node:", i>>)

\* skip unused logs
SkipUnusedLogline ==
    /\ \/ /\ LoglineIsEvent("SendAppendEntriesResponse")
          /\ logline.event.msg.from # logline.event.msg.to
       \/ /\ LoglineIsEvent("SendRequestVoteResponse")
          /\ logline.event.msg.from # logline.event.msg.to
       \/ LoglineIsEvent("BecomeFollower")
    /\ PrintT(<<"skip", "line:", l, "event:", logline.event.name>>)
    /\ StepToNextTrace
    /\ UNCHANGED <<vars, history>>

TraceNext ==
    \/ \E i,j \in Server : RequestVoteIfLogged(i, j)
    \/ \E i \in Server : BecomeLeaderIfLogged(i)
    \/ \E i \in Server : ClientRequestIfLogged(i, 0)
    \/ \E i \in Server : AdvanceCommitIndexIfLogged(i)
    \/ \E i,j \in Server : AppendEntriesIfLogged(i, j)
    \/ \E m \in DOMAIN messages : ReceiveIfLogged(m)
    \/ \E i \in Server : TimeoutIfLogged(i)
    \/ SkipUnusedLogline
 

TraceSpec ==
    TraceInit /\ [][TraceNext]_<<l, vars>>

-------------------------------------------------------------------------------------

TraceView ==
    \* A high-level state  s  can appear multiple times in a system trace.  Including the
     \* current level in TLC's view ensures that TLC will not stop model checking when  s
     \* appears the second time in the trace.  Put differently,  TraceView  causes TLC to
     \* consider  s_i  and s_j  , where  i  and  j  are the positions of  s  in the trace,
     \* to be different states.
    <<vars, l>>

-------------------------------------------------------------------------------------

\* The property TraceMatched below will be violated if TLC runs with more than a single worker.
ASSUME TLCGet("config").worker = 1

TraceMatched ==
    \* We force TLC to check TraceMatched as a temporal property because TLC checks temporal
    \* properties after generating all successor states of the current state, unlike
    \* invariants that are checked after generating a successor state.
    \* If the queue is empty after generating all successors of the current state,
    \* and l is less than the length of the trace, then TLC failed to validate the trace.
    \*
    \* We allow more than a single successor state to accept traces like suffix_collision.1
    \* and fancy_election.1.  The trace suffix_collision.1 at h_ts 466 has a follower receiving
    \* an AppendEntries request.  At that point in time, there are two AE requests contained in
    \* the variable messages. However, the loglines before h_ts 506 do not allow us to determine
    \* which request it is.
    \*
    \* Note: Consider changing {1,2} to (Nat \ {0}) while validating traces with holes.
    [](l <= Len(TraceLog) => [](TLCGet("queue") \in {1,2} \/ l > Len(TraceLog)))

==================================================================================
