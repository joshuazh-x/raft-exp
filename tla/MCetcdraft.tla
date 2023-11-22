--------------------------------- MODULE MCetcdraft ---------------------------------
EXTENDS etcdraft, Functions, TLC

\* Constraints
MaxLogLength == Cardinality(Server) + 2 \* etcd bootstrap will add some conf change entries
MaxRestarts == 1
MaxTimeouts == 1
MaxClientRequests == 2
MaxTerms == MaxTimeouts + 2 \* +2 since we init state with first leader elected
MaxMembershipChanges == 1
MaxTriedMembershipChanges == MaxMembershipChanges + 1
MaxInFlightMessages == LET card == Cardinality(Server) IN 2 * card * card
MaxAuditLogLen == 30

R == INSTANCE etcdraft

\* history variable used to constraining the search space
\* restarted: how many times each server restarted
VARIABLE
    \* @typeAlias: ACTION = [action: Str, executedOn: Int, msg: MSG];
    \* @type: [server: Int -> [restarted: Int, timeout: Int], global: Seq(ACTION), hadNumLeaders: Int, hadNumClientRequests: Int, hadNumSubTermChanges: Int];
    history

MCReplicate(i, data, type) ==
    /\ R!Replicate(i, data, type)
    /\ IF type = ConfigEntry THEN 
        history' = [history EXCEPT !["hadNumTriedMembershipChanges"]=@+1]
       ELSE 
        UNCHANGED <<history>>

MCApplySimpleConfChangeInLeader(i) ==
    /\ R!ApplySimpleConfChangeInLeader(i) 
    /\ IF log[i].entries[pendingConfChangeIndex[i]].type = ConfigEntry THEN 
        history' = [history EXCEPT !["hadNumMembershipChanges"]=@+1]
       ELSE 
        UNCHANGED <<history>>

MCSendDirect(m) ==
    /\ R!SendDirect(m)
    /\ LET msgAction == [action |-> "Send", executedOn |-> m.msource, msg |-> m]
       IN history' = [history EXCEPT !["global"] = Append(@, msgAction)]

MCDiscardDirect(m) ==
    /\ R!DiscardDirect(m)
    /\ LET action == [action |-> "Receive", executedOn |-> m.mdest, msg |-> m] 
       IN history' = [history EXCEPT !["global"] = Append(@, action)]

MCReplyDirect(response, request) ==
    /\ R!ReplyDirect(response, request)
    /\ 
     LET req == request
        resp == response
        recvA == [action |-> "Receive", executedOn |-> request.mdest, msg |-> req]
        respA == [action |-> "Send", executedOn |-> response.msource, msg |-> resp]
     IN history' = [history EXCEPT !["global"] = Append(Append(@, recvA), respA)]

VARIABLE debug

MCDuplicateMessage(m) ==
    /\ UNCHANGED history
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "DuplicateMessage")]
    /\ R!DuplicateMessage(m)

MCDropMessage(m) ==
    /\ UNCHANGED history
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "DropMessage")]
    /\ R!DropMessage(m)

MCRestart(i) ==
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "Restart")]
    /\ history' = [history EXCEPT
                                !["server"] [i] ["restarted"] = @ + 1,
                                !["global"] = Append(@, [action |-> "Restart", executedOn |-> i])]
    /\ R!Restart(i)

MCUpdateTerm(i, j, m) ==
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "UpdateTerm")]
    /\ history'        = [history EXCEPT !["global"] = Append(@, [action |-> "UpdateTerm", executedOn |-> i, msg |-> m])]
    /\ R!UpdateTerm(i, j, m)

MCDropStaleResponse(i, j, m) ==
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "DropStaleResponse")]
    /\ history' = [history EXCEPT !["global"] = Append(@, [action |-> "DropStaleResponse", executedOn |-> i, msg |-> m])]
    /\ R!DropStaleResponse(i, j, m)

MCHandleAppendEntriesResponse(i, j, m) ==
    \/ /\ \lnot m.msuccess \* not successful
       /\ UNCHANGED <<debug>>
    \/ /\ m.msuccess \* not successful
       /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "HandleAppendEntriesResponse")]
    /\ R!HandleAppendEntriesResponse(i, j, m)

MCHandleAppendEntriesRequest(i, j, m) ==
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "HandleAppendEntriesRequest")]
    /\ UNCHANGED history
    /\ R!HandleAppendEntriesRequest(i, j, m)

MCHandleRequestVoteResponse(i, j, m) ==
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "HandleRequestVoteResponse")]
    /\ R!HandleRequestVoteResponse(i, j, m)

MCHandleRequestVoteRequest(i, j, m) ==
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "HandleRequestVoteRequest")]
    /\ UNCHANGED history
    /\ R!HandleRequestVoteRequest(i, j, m)

MCDeleteServer(i, j) ==
    /\ UNCHANGED <<debug>>
    /\ R!DeleteServer(i, j)

MCAddNewServer(i, j) ==
    /\ UNCHANGED <<debug>>
    /\ R!AddNewServer(i, j)

MCAddLearner(i, j) ==
    /\ UNCHANGED <<debug>>
    /\ R!AddLearner(i, j)

MCAdvanceCommitIndex(i) ==
    /\ debug' = [debug EXCEPT !["debugSeq"] = Append(debug["debugSeq"], "AdvanceCommitIndex"),
                              !["auditLog"] = Append(debug["auditLog"], "AdvanceCommitIndex")]
    /\ R!AdvanceCommitIndex(i)
    /\ LET newCommitIndex == commitIndex'[i]
           committed == newCommitIndex > commitIndex[i]
       IN 
        /\ IF committed THEN
             history' = [history EXCEPT
                !["global"] = Append(@, [action |-> "CommitEntry", executedOn |-> i, entry |-> log[i].entries[newCommitIndex]])]
           ELSE UNCHANGED <<history>>

MCClientRequest(i, v) ==
    /\ debug' = [debug EXCEPT !["debugSeq"] = Append(debug["debugSeq"], "ClientRequest"),
                              !["auditLog"] = Append(debug["auditLog"], "ClientRequest")]
    /\ history'    = [history EXCEPT !["hadNumClientRequests"] = @ + 1]
    /\ R!ClientRequest(i, v)

MCBecomeLeader(i) ==
    /\ debug' = [debug EXCEPT !["debugSeq"] = Append(debug["debugSeq"], "BecomeLeader"),
                              !["auditLog"] = Append(debug["auditLog"], "BecomeLeader")]
    /\ history'    = [history EXCEPT 
                            !["hadNumLeaders"] = @ + 1,
                            !["global"] = Append(@, 
                                [action |-> "BecomeLeader", executedOn |-> i, leaders |-> (CurrentLeaders \cup {i})])]
     /\ R!BecomeLeader(i)

MCAppendEntries(i, j, range) ==
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "AppendEntries")]
    /\ R!AppendEntries(i, j, range)

MCRequestVote(i, j) ==
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "RequestVote")]
    /\ R!RequestVote(i, j)

MCTimeout(i) ==
    /\ debug' = [debug EXCEPT !["auditLog"] = Append(debug["auditLog"], "Timeout")]
    /\ history'        = [history EXCEPT 
                              !["server"] [i] ["timeout"] = @ + 1,
                              !["global"] = Append(@, [action |-> "Timeout", executedOn |-> i])]
    /\ R!Timeout(i)
    
MCInitDebug == [ 
    flag |-> FALSE,
    debugInfo |-> "",
    debugSeq |-> << >>,
    auditLog |-> << >>
]

InitHistory == [
    server |-> [i \in Server |-> [restarted |-> 0, timeout |-> 0]],
    global |-> << >>,
    hadNumLeaders |-> 1,
    hadNumClientRequests |-> 0,
    hadNumTriedMembershipChanges |-> 0,
    hadNumMembershipChanges |-> 0
]

MCInit ==
    /\ R!Init
    /\ debug = MCInitDebug
    /\ history  = InitHistory

MCvars ==
    << vars, debug, history >>

ClientRequestConditional == history["hadNumClientRequests"] < MaxClientRequests /\ \E i \in Server : ClientRequest(i, 0)
TimeoutConditional == \A j \in Server: history["server"][j]["timeout"] < MaxTimeouts /\ \E i \in Server : Timeout(i)

NextAsyncConditional == 
    \/ \E i,j \in Server : RequestVote(i, j)
    \/ \E i \in Server : BecomeLeader(i)
    \/ ClientRequestConditional
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i,j \in Server : \E b,e \in matchIndex[i][j]+1..log[i].len+1 : AppendEntries(i, j, <<b,e>>)
    \/ \E i,j \in Server : Heartbeat(i, j)
    \/ \E i,j \in Server : \E index \in 1..commitIndex[i] : SendSnapshot(i, j, index)
    \/ NextRequestVoteRequest
    \/ NextRequestVoteResponse
    \/ NextAppendEntriesRequest
    \/ NextAppendEntriesResponse
    \/ TimeoutConditional
    \/ \E i \in Server : Ready(i)
    \/ \E i \in Server : StepDownToFollower(i)

NextCrashConditional == \A j \in Server: history["server"][j]["restarted"] < MaxRestarts /\ \E i \in Server : Restart(i)

NextConditional == 
    \/ NextAsyncConditional
    \/ NextCrashConditional
    \/ NextUnreliable


\* Constraints to make model checking more feasible

BoundedInFlightMessages == BagCardinality(messages) + BagCardinality(pendingMessages) <= MaxInFlightMessages

BoundedLogSize == \A i \in Server: log[i].len <= MaxLogLength

BoundedRestarts == \A i \in Server: history["server"][i]["restarted"] <= MaxRestarts

BoundedTimeouts == \A i \in Server: history["server"][i]["timeout"] <= MaxTimeouts

BoundedTerms == \A i \in Server: currentTerm[i] <= MaxTerms

BoundedClientRequests == history["hadNumClientRequests"] <= MaxClientRequests

BoundedTriedMembershipChanges == history["hadNumTriedMembershipChanges"] <= MaxTriedMembershipChanges

BoundedMembershipChanges == history["hadNumMembershipChanges"] <= MaxMembershipChanges

ElectionsUncontested == Cardinality({c \in DOMAIN state : state[c] = Candidate}) <= 1

CleanStartUntilFirstRequest ==
    ((history["hadNumLeaders"] < 1 /\ history["hadNumClientRequests"] < 1)) =>
    /\ \A i \in Server: history["server"][i]["restarted"] = 0
    /\ FoldFunction(+, 0, [i \in Server |-> history["server"][i]["timeout"]]) <= 1        
    /\ ElectionsUncontested

CleanStartUntilTwoLeaders ==
    (history["hadNumLeaders"] < 2) =>
    /\ FoldFunction(+, 0, [i \in Server |-> history["server"][i]["restarted"]]) <= 1      
    /\ FoldFunction(+, 0, [i \in Server |-> history["server"][i]["timeout"]]) <= 2        

-----

\* Generate interesting traces

BoundedTrace == Len(history["global"]) <= 30

FirstBecomeLeader == ~ \E i \in DOMAIN history["global"] :
    history["global"][i].action = "BecomeLeader"

FirstCommit == ~ \E i \in Server : commitIndex[i] > 0

CoverageDepthCalculate == \/ ~ \E i \in Server: commitIndex[i] > 1 \* At least append 2 entries for data consistency check
                          \/ Cardinality({k \in DOMAIN history["global"]: history["global"][k].action = "CommitEntry"}) < 2
                          \/ ~ \E j \in Server : history["server"][j]["restarted"] >= 1 \* At least 1 restart
                          \/ history["hadNumLeaders"] < 2 \* At least reelect leader

FirstRestart == ~ \E i \in Server : history["server"][i]["restarted"] >= 2

LeadershipChange == history["hadNumLeaders"] < 2

MembershipChange == history["hadNumMembershipChanges"] < 1

MultipleMembershipChanges == history["hadNumMembershipChanges"] < 2

ConcurrentLeaders == ~ (Cardinality(CurrentLeaders) >= 2)

EntryCommitted == ~
    \E i \in DOMAIN history["global"] :
    /\ LET x == history["global"][i] IN
        /\ x.action = "CommitEntry"

CommitWhenConcurrentLeaders == ~
    \E i, k \in DOMAIN history["global"] :
    /\ i < k
    /\ LET  x == history["global"][i]
            y == history["global"][k]
        IN
        /\ x.action = "BecomeLeader" /\ Cardinality(x.leaders) >= 2
        /\ y.action = "CommitEntry"
    \* Run for a few more steps
    /\ Len(history["global"]) >= k + 2
    \* Still have concurrent leaders
    /\ Cardinality(CurrentLeaders) >= 2

\* A constraint to ease finding a violation of CommitWhenConcurrentLeaders:
\* the shortest trace (using NextAsync) where ConcurrentLeaders is vZiolated
\* has length 20, so we constrain the search space given the fact that
\* CommitWhenConcurrentLeaders implies ConcurrentLeaders held in the past.
CommitWhenConcurrentLeaders_constraint ==
    (Len(history["global"]) >= 20) =>
        \E i \in DOMAIN history["global"] :
            LET x == history["global"][i] IN
            x.action = "BecomeLeader" /\ Cardinality(x.leaders) >= 2

\* BUT, in fact, this does not get us a tremendous boost. When the trace gets
\* long enough, there are many ways to satisfy a particular constraint, so
\* you still get hit by state space explosion. For example, there are over 1.2 million
\*  traces of length 20 that satisfy CommitWhenConcurrentLeaders_constraint.
\* But we can use the fact that:
\*      CommitWhenConcurrentLeaders => ConcurrentLeaders on a prefix of the trace
\* to great effect!
\*
\* Reference: "punctuated search" in Michaels et al (Eurosys 2019).

CommitWhenConcurrentLeaders_unique ==
    \E s1, s2, s3 \in Server :
        /\ Cardinality({s1, s2, s3}) = 3
        /\ LET  ConcurrentLeaders_trace == [global |-> <<[action |-> "Timeout", executedOn |-> s1], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s1, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s2, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s2, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "BecomeLeader", executedOn |-> s1, leaders |-> {s1}], [action |-> "Timeout", executedOn |-> s2], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s3, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s3, msg |-> [mdest |-> s3, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s3, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s3, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s3, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "BecomeLeader", executedOn |-> s2, leaders |-> {s1, s2}]>>, hadNumClientRequests |-> 0, hadNumLeaders |-> 2, hadNumMembershipChanges |-> 0, hadNumTriedMembershipChanges |-> 0, server |-> (s1 :> [restarted |-> 0, timeout |-> 1] @@ s2 :> [restarted |-> 0, timeout |-> 1] @@ s3 :> [restarted |-> 0, timeout |-> 0])]
                maxLen == Min({Len(ConcurrentLeaders_trace["global"]), Len(history["global"])})
                prefix == SubSeq(ConcurrentLeaders_trace["global"], 1, maxLen)
            IN IsPrefix(prefix, history["global"])

\* We can also constrain the future via action constraints.
CommitWhenConcurrentLeaders_action_constraint ==
    (Len(history["global"]) >= 20) =>
        \* No timeouts
        /\ \A i \in Server : state'[i] /= Candidate

MajorityOfClusterRestarts == ~
    \* We want some non-trivial logs
    /\ \E i, j \in Server :
        /\ i /= j
        /\ log[i].len >= 2
        /\ log[j].len >= 1
    /\ \E maj \in Quorums[GetConfig(Server)] :
        \A i \in maj: history["server"][i]["restarted"] >= 1
    \* There is activity between the restarts
    /\ \A i, k \in DOMAIN history["global"] :
        (
        /\ (i < k)
        /\ history["global"][i].action = "Restart"
        /\ history["global"][k].action = "Restart"
        ) => (k - i) >= 6

MajorityOfClusterRestarts_constraint ==
    \E s1, s2, s3 \in Server :
        /\ Cardinality({s1, s2, s3}) = 3
        /\ LET  CommitWhenConcurrentLeaders_trace == [global |-> <<[action |-> "Timeout", executedOn |-> s1], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s1, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s2, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s2, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s1, msg |-> [mdest |-> s1, mlog |-> <<>>, msource |-> s1, mterm |-> 2, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "BecomeLeader", executedOn |-> s1, leaders |-> {s1}], [action |-> "Timeout", executedOn |-> s2], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s3, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s3, msg |-> [mdest |-> s3, mlastLogIndex |-> 0, mlastLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteRequest"]], [action |-> "Send", executedOn |-> s3, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s3, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s3, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mlog |-> <<>>, msource |-> s2, mterm |-> 3, mtype |-> "RequestVoteResponse", mvoteGranted |-> TRUE]], [action |-> "BecomeLeader", executedOn |-> s2, leaders |-> {s1, s2}], [action |-> "Send", executedOn |-> s1, msg |-> [mcommitIndex |-> 0, mdest |-> s2, mentry |-> <<[term |-> 2, type |-> "ValueEntry", value |-> 1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "AppendEntriesRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mcommitIndex |-> 0, mdest |-> s3, mentry |-> <<[term |-> 3, type |-> "ValueEntry", value |-> 2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "AppendEntriesRequest"]], [action |-> "Receive", executedOn |-> s3, msg |-> [mcommitIndex |-> 0, mdest |-> s3, mentry |-> <<[term |-> 3, type |-> "ValueEntry", value |-> 2]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, msource |-> s2, mterm |-> 3, mtype |-> "AppendEntriesRequest"]], [action |-> "Send", executedOn |-> s3, msg |-> [mdest |-> s2, mmatchIndex |-> 1, msource |-> s3, msuccess |-> TRUE, mterm |-> 3, mtype |-> "AppendEntriesResponse"]], [action |-> "Receive", executedOn |-> s2, msg |-> [mdest |-> s2, mmatchIndex |-> 1, msource |-> s3, msuccess |-> TRUE, mterm |-> 3, mtype |-> "AppendEntriesResponse"]], [action |-> "CommitEntry", entry |-> [term |-> 3, type |-> "ValueEntry", value |-> 2], executedOn |-> s2], [action |-> "Receive", executedOn |-> s2, msg |-> [mcommitIndex |-> 0, mdest |-> s2, mentry |-> <<[term |-> 2, type |-> "ValueEntry", value |-> 1]>>, mprevLogIndex |-> 0, mprevLogTerm |-> 0, msource |-> s1, mterm |-> 2, mtype |-> "AppendEntriesRequest"]], [action |-> "Send", executedOn |-> s2, msg |-> [mdest |-> s1, mmatchIndex |-> 0, msource |-> s2, msuccess |-> FALSE, mterm |-> 3, mtype |-> "AppendEntriesResponse"]]>>, hadNumClientRequests |-> 2, hadNumLeaders |-> 2, hadNumMembershipChanges |-> 0, hadNumTriedMembershipChanges |-> 0, server |-> (s1 :> [restarted |-> 0, timeout |-> 1] @@ s2 :> [restarted |-> 0, timeout |-> 1] @@ s3 :> [restarted |-> 0, timeout |-> 0])]
                maxLen == Min({Len(CommitWhenConcurrentLeaders_trace["global"]), Len(history["global"])})
                prefix == SubSeq(CommitWhenConcurrentLeaders_trace["global"], 1, maxLen)
            IN IsPrefix(prefix, history["global"])

AddSucessful == ~ \E i \in DOMAIN history["global"] :
    history["global"][i].action = "AddServer"

AddCommits == ~
    \E i, j \in DOMAIN history["global"] :
    /\ i < j
    /\ LET  x == history["global"][i]
            y == history["global"][j]
        IN
        /\ x.action = "AddServer"
        /\ y.action = "CommitMembershipChange"
        /\ x.added \in y.config

NewlyJoinedBecomeLeader == ~
    \E i, j \in DOMAIN history["global"] :
    /\ i < j
    /\ LET  x == history["global"][i]
            y == history["global"][j]
        IN
        /\ x.action = "AddServer"
        /\ y.action = "BecomeLeader"
        /\ x.added = y.executedOn

LeaderChangesDuringConfChange == ~
    \E i, k \in DOMAIN history["global"] :
    /\ i < k
    /\ LET  x == history["global"][i]
            y == history["global"][k]
        IN
        /\ x.action = "AddServer"
        /\ y.action = "BecomeLeader"
    \* The membership change does not commit before the leader changes
    /\ ~ \E j \in i..k :
        /\ history["global"][j].action = "CommitMembershipChange"

-------------------------------------------------------------------------------

\* Constraints to make model checking more feasible

BoundedAuditLog == Len(debug["auditLog"]) <= MaxAuditLogLen

===============================================================================