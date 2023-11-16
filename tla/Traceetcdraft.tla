-------------------------------- MODULE Traceetcdraft -------------------------------
EXTENDS etcdraft, Json, IOUtils, Sequences

\* raft.pb.go enum MessageType
RaftMsgType ==
    "MsgApp" :> AppendEntriesRequest @@ "MsgAppResp" :> AppendEntriesResponse @@
    "MsgVote" :> RequestVoteRequest @@ "MsgVoteResp" :> RequestVoteResponse @@
    "MsgHeartbeat" :> AppendEntriesRequest @@ "MsgHeartbeatResp" :> AppendEntriesResponse @@
    "MsgSnap" :> AppendEntriesRequest

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

TraceServer == FoldSeq(
    LAMBDA x, y: y \cup IF  /\ x.event.name = "ChangeConf" 
                            /\ "changes" \in DOMAIN x.event.prop.cc
                            /\ x.event.prop.cc.changes[1].action \in {"AddNewServer", "AddLearner"}
                            THEN {x.event.nid, x.event.prop.cc.changes[1].nid} 
                            ELSE {x.event.nid},
    {}, TraceLog)
-------------------------------------------------------------------------------------
ConfFromLog(l) == << ToSet(l.event.conf[1]), ToSet(l.event.conf[2]) >>

FirstInitStatesLog(i) ==
    LET initStatesLogOfNode == {k \in DOMAIN TraceLog: TraceLog[k].event.nid = i /\ TraceLog[k].event.name = "InitState"}
    IN  IF initStatesLogOfNode = {} THEN 
            [
                event |-> [
                    state |-> [
                        term |-> 0,
                        vote |-> "",
                        commit |-> 0 ],
                    role |-> "",
                    conf |-> << <<>>, <<>> >> ]
            ] 
        ELSE TraceLog[Min(initStatesLogOfNode)]

TraceInitServer == ToSet(TraceLog[1].event.conf[1])
ASSUME TraceInitServer \subseteq TraceServer

MakeBootstrappedLog(i) == 
    LET 
        fil == FirstInitStatesLog(i)
        n == fil.event.state.commit
        prefix == [j \in 1..n-1 |-> [term  |-> 1, type |-> ConfigEntry]]
    IN 
        IF n > 0 THEN 
            Append(prefix, [    term  |-> 1, 
                                type |-> ConfigEntry, 
                                value |-> [ newconf |-> ConfFromLog(fil)[1] ]
                            ]) 
        ELSE 
            <<>>
    

TraceInitDurableState == 
    /\ durableState = [
        \* serverVars
        currentTerm |-> [i \in Server |-> FirstInitStatesLog(i).event.state.term],
        state |-> [i \in Server |-> FirstInitStatesLog(i).event.role],
        votedFor |-> [i \in Server |-> FirstInitStatesLog(i).event.state.vote],
        \* logVars
        commitIndex |-> [i \in Server |-> FirstInitStatesLog(i).event.state.commit],
        log |-> [i \in Server |-> MakeBootstrappedLog(i)],
        \* confVars
        pendingConfChangeIndex |-> [i \in Server |-> 0],
        config |->[ i \in Server |-> ConfFromLog(FirstInitStatesLog(i)) ] ]

OneMoreMessage(msg) ==
    \/ msg \notin DOMAIN pendingMessages /\ msg \in DOMAIN pendingMessages' /\ pendingMessages'[msg] = 1
    \/ msg \in DOMAIN pendingMessages /\ messages'[msg] = pendingMessages[msg] + 1

OneLessMessage(msg) ==
    \/ msg \in DOMAIN messages /\ messages[msg] = 1 /\ msg \notin DOMAIN messages'
    \/ msg \in DOMAIN messages /\ messages'[msg] = messages[msg] - 1

-------------------------------------------------------------------------------------

VARIABLE l
logline == TraceLog[l]

TraceInit ==
    /\ l = 1
    /\ logline = TraceLog[l]
    /\ Init

StepToNextTrace == 
    /\ l' = l+1

StepToNextTraceIfMessageIsProcessed(msg) ==
    IF OneLessMessage(msg) 
        THEN StepToNextTrace
        ELSE UNCHANGED <<l>>

-------------------------------------------------------------------------------------

LoglineIsEvent(e) ==
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
    /\ (\lnot logline.event.msg.reject) => m.mmatchIndex = logline.event.msg.index

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

ValidateStates(i) ==
    /\ currentTerm'[i] = logline.event.state.term
    /\ state'[i] = logline.event.role
    /\ votedFor'[i] = logline.event.state.vote
    /\ Len(log'[i]) = logline.event.log
    /\ commitIndex'[i] = logline.event.state.commit
    /\ config'[i] = ConfFromLog(logline)

\* perform RequestVote transition if logline indicates so
ValidateAfterRequestVote(i, j) == 
    /\ ValidateStates(i)
    /\ \E m \in DOMAIN pendingMessages':
       /\ \/ LoglineIsRequestVoteRequest(m)
          \/ /\ LoglineIsRequestVoteResponse(m)
             /\ m.msource = m.mdest
       /\ OneMoreMessage(m)

RequestVoteIfLogged(i, j) ==
    /\ \/ LoglineIsMessageEvent("SendRequestVoteRequest", i, j)
       \* etcd candidate sends MsgVoteResp to itself upon compain starting
       \/ /\ LoglineIsMessageEvent("SendRequestVoteResponse", i, j)
          /\ i = j 
    /\ RequestVote(i, j)
    /\ ValidateAfterRequestVote(i, j)

\* perform BecomeLeader transition if logline indicates so
ValidateAfterBecomeLeader(i) == 
    /\ ValidateStates(i)
    /\ logline.event.role = "StateLeader"
    /\ state'[i] = Leader
    
BecomeLeaderIfLogged(i) ==
    /\ LoglineIsNodeEvent("BecomeLeader", i)
    /\ BecomeLeader(i)
    /\ ValidateAfterBecomeLeader(i)

\* perform ClientRequest transition if logline indicates so
ClientRequestIfLogged(i, v) == 
    /\ LoglineIsNodeEvent("Replicate", i)
    /\ ClientRequest(i, v)

\* perform AdvanceCommitIndex transition if logline indicates so
ValidateAfterAdvanceCommitIndex(i) ==
    /\ ValidateStates(i)
    /\ logline.event.role = "StateLeader"
    /\ state[i] = Leader

AdvanceCommitIndexIfLogged(i) ==
    /\ LoglineIsNodeEvent("Commit", i)
    /\ AdvanceCommitIndex(i)
    /\ ValidateAfterAdvanceCommitIndex(i)    

\* perform AppendEntries transition if logline indicates so
ValidateAfterAppendEntries(i, j) ==
    /\ ValidateStates(i)
    /\ \E msg \in DOMAIN pendingMessages':
        /\ \/ LoglineIsAppendEntriesRequest(msg)
           \/ /\ LoglineIsAppendEntriesResponse(msg)
              /\ msg.msource = msg.mdest
        \* There is now one more message of this type.
        /\ OneMoreMessage(msg)

AppendEntriesIfLogged(i, j, range) == 
    /\ \/ /\ LoglineIsMessageEvent("SendAppendEntriesRequest", i, j)
          /\ \/ /\ logline.event.msg.type = "MsgApp"
                /\ range[1] = logline.event.msg.index + 1
                /\ range[2] = range[1] + logline.event.msg.entries
             \/ /\ logline.event.msg.type = "MsgHeartbeat"
                /\ range[1] = logline.event.msg.commit + 1
                /\ range[2] = range[1]
             \/ /\ logline.event.msg.type = "MsgSnapshot"
                /\ range[1] = 1 
                /\ range[2] = 1 + logline.event.msg.entries
       \* etcd leader sends MsgAppResp to itself after appending log entry
       \/ /\ LoglineIsMessageEvent("SendAppendEntriesResponse", i, j)
          /\ i = j
    /\ AppendEntries(i, j, range)
    /\ ValidateAfterAppendEntries(i, j)

ReceiveMessageTraceNames == { "ReceiveAppendEntriesRequest", "ReceiveAppendEntriesResponse", "ReceiveRequestVoteRequest", "ReceiveRequestVoteResponse", "ReceiveSnapshot" }
\* perform Receive transition if logline indicates so
LoglineIsReceivedMessage(m) ==
    \/ /\ LoglineIsEvent("ReceiveAppendEntriesRequest")
       /\ LoglineIsAppendEntriesRequest(m)
    \/ /\ LoglineIsEvent("ReceiveAppendEntriesResponse")
       /\ LoglineIsAppendEntriesResponse(m)
    \/ /\ LoglineIsEvent("ReceiveRequestVoteRequest")
       /\ LoglineIsRequestVoteRequest(m) 
    \/ /\ LoglineIsEvent("ReceiveRequestVoteResponse")
       /\ LoglineIsRequestVoteResponse(m)
    \/ /\ LoglineIsEvent("ReceiveSnapshot")
       /\ LoglineIsAppendEntriesRequest(m)

ReceiveIfLogged(m) == 
    /\ LoglineIsReceivedMessage(m)
    /\ Receive(m)

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

\* perform AddNewServer transition if logline indicates so
AddNewServerIfLogged(i, j) ==
    /\ LoglineIsNodeEvent("ChangeConf", i)
    /\ Len(logline.event.prop.cc.changes) = 1
    /\ logline.event.prop.cc.changes[1].action = "AddNewServer"
    /\ logline.event.prop.cc.changes[1].nid = j
    /\ AddNewServer(i, j)

\* perform DeleteServer transition if logline indicates so
DeleteServerIfLogged(i, j) ==
    /\ LoglineIsNodeEvent("ChangeConf", i)
    /\ Len(logline.event.prop.cc.changes) = 1
    /\ logline.event.prop.cc.changes[1].action = "RemoveServer"
    /\ logline.event.prop.cc.changes[1].nid = j
    /\ DeleteServer(i, j)
    

\* perform ApplyConfChangeInLeader transition if logline indicates so
ApplySimpleConfChangeInLeaderIfLogged(i) ==
    /\ LoglineIsNodeEvent("ApplyConfChange", i)
    /\ logline.event.role = "StateLeader"
    /\ ApplySimpleConfChangeInLeader(i)

ReadyIfLogged(i) ==
    /\ LoglineIsNodeEvent("Ready", i)
    /\ Ready(i)

RestartIfLogged(i) ==
    /\ LoglineIsNodeEvent("InitState", i)
    /\ Restart(i)
    /\ ValidateStates(i)

LoglineIsBecomeFollowerInUpdateTerm ==
    /\ LoglineIsEvent("BecomeFollower")
    /\ LET 
            k == SelectLastInSubSeq(TraceLog, 1, l-1, LAMBDA x: x.event.nid = logline.event.nid)
       IN 
            /\ k > 0 
            /\ TraceLog[k].event.name \in ReceiveMessageTraceNames
            /\ TraceLog[k].event.state.term < TraceLog[k].event.msg.term
            /\ TraceLog[k].event.msg.term = logline.event.state.term

BecomeFollowerIfLogged(i, t) ==
    /\ LoglineIsNodeEvent("BecomeFollower", i)
    /\ \lnot LoglineIsBecomeFollowerInUpdateTerm
    /\ BecomeFollowerOfTerm(i, t)
    /\ ValidateStates(i)

\* skip unused logs
SkipUnusedLogline ==
    /\ \/ /\ LoglineIsEvent("SendAppendEntriesResponse")
          /\ logline.event.msg.from # logline.event.msg.to
       \/ /\ LoglineIsEvent("SendRequestVoteResponse")
          /\ logline.event.msg.from # logline.event.msg.to
       \/ LoglineIsBecomeFollowerInUpdateTerm
       \/ /\ LoglineIsEvent("ApplyConfChange")
          /\ logline.event.role # "StateLeader"
    /\ UNCHANGED <<vars>>

\* Next actions where each one 
TraceNextNonReceiveActions ==
    /\ \/ \E i,j \in Server : RequestVoteIfLogged(i, j)
       \/ \E i \in Server : BecomeLeaderIfLogged(i)
       \/ \E i \in Server : ClientRequestIfLogged(i, 0)
       \/ \E i \in Server : AdvanceCommitIndexIfLogged(i)
       \/ \E i,j \in Server: \E b,e \in 1..Len(log[i])+1: AppendEntriesIfLogged(i, j, <<b,e>>)
       \/ \E i \in Server : TimeoutIfLogged(i)
       \/ \E i,j \in Server: AddNewServerIfLogged(i, j)
       \/ \E i,j \in Server: DeleteServerIfLogged(i, j)
       \/ \E i \in Server: ApplySimpleConfChangeInLeaderIfLogged(i)
       \/ \E i \in Server: ReadyIfLogged(i)
       \/ \E i \in Server: RestartIfLogged(i)
       \/ \E i \in Server: \E t \in currentTerm[i]..FoldSeq(LAMBDA x,y: Max({x,y}), 0, currentTerm): BecomeFollowerIfLogged(i, t)
       \/ SkipUnusedLogline
    /\ StepToNextTrace

TraceNextReceiveActions ==
    \E m \in DOMAIN messages : 
        /\ ReceiveIfLogged(m)
        /\ StepToNextTraceIfMessageIsProcessed(m)

TraceNext ==
    \/ TraceNextNonReceiveActions
    \/ TraceNextReceiveActions
 
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

etcd == INSTANCE etcdraft
etcdSpec == etcd!Init /\ [][etcd!NextDynamic]_etcd!vars

==================================================================================


