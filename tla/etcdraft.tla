--------------------------------- MODULE etcdraft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro, 2015 Brandon Amos and Huanchen Zhang,
\* 2016 Daniel Ricketts, 2021 George Pîrlea and Darius Foo.
\*
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, Integers, Bags, FiniteSets, Sequences, SequencesExt, FiniteSetsExt, TLC

\* The initial and global set of server IDs.
CONSTANTS InitServer, Server

\* Log metadata to distinguish values from configuration changes.
CONSTANT ValueEntry, ConfigEntry

\* Constraints
MaxLogLength == 5
MaxRestarts == 2
MaxTimeouts == 3
MaxClientRequests == 3
MaxTerms == MaxTimeouts + 1
MaxMembershipChanges == 3
MaxTriedMembershipChanges == MaxMembershipChanges + 1
MaxInFlightMessages == LET card == Cardinality(Server) IN 2 * card * card

\* Server states.
CONSTANTS 
    \* @type: Str;
    Follower,
    \* @type: Str;
    Candidate,
    \* @type: Str;
    Leader

\* A reserved value.
CONSTANTS 
    \* @type: Int;
    Nil

\* Message types:
CONSTANTS 
    \* @type: Str;
    RequestVoteRequest,
    \* @type: Str;
    RequestVoteResponse,
    \* @type: Str;
    AppendEntriesRequest,
    \* @type: Str;
    AppendEntriesResponse

-----

\* Message types

EmptyRVReqMsg == [
    mtype         |-> RequestVoteRequest,
    mterm         |-> 0,
    mlastLogTerm  |-> 0,
    mlastLogIndex |-> 0,
    msource       |-> Nil,
    mdest         |-> Nil
]

EmptyAEReqMsg == [
    mtype          |-> AppendEntriesRequest,
    mterm          |-> 0,
    mprevLogIndex  |-> 0,
    mprevLogTerm   |-> 0,
    mentries       |-> << >>,
    mcommitIndex   |-> Nil,
    msource        |-> Nil,
    mdest          |-> Nil
]

EmptyRVRespMsg == [
    mtype        |-> RequestVoteResponse,
    mterm        |-> Nil,
    mvoteGranted |-> FALSE,
    mlog         |-> << >>,
    msource      |-> Nil,
    mdest        |-> Nil
]

EmptyAERespMsg == [
    mtype           |-> AppendEntriesResponse,
    mterm           |-> 0,
    msuccess        |-> FALSE,
    mmatchIndex     |-> 0,
    msource         |-> Nil,
    mdest           |-> Nil
]

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. We differentiate between the message types to support Apalache.
VARIABLE
    \* @typeAlias: ENTRY = [term: Int, value: Int];
    \* @typeAlias: LOGT = Seq(ENTRY);
    \* @typeAlias: RVREQT = [mtype: Str, mterm: Int, mlastLogTerm: Int, mlastLogIndex: Int, msource: Int, mdest: Int];
    \* @typeAlias: RVRESPT = [mtype: Str, mterm: Int, mvoteGranted: Bool, mlog: LOGT, msource: Int, mdest: Int ];
    \* @typeAlias: AEREQT = [mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: LOGT, mcommitIndex: Int, msource: Int, mdest: Int ];
    \* @typeAlias: AERESPT = [mtype: Str, mterm: Int, msuccess: Bool, mmatchIndex: Int, msource: Int, mdest: Int ];
    \* @typeAlias: MSG = [ wrapped: Bool, mtype: Str, mterm: Int, msource: Int, mdest: Int, RVReq: RVREQT, RVResp: RVRESPT, AEReq: AEREQT, AEResp: AERESPT ];
    \* @type: MSG -> Int;
    messages
VARIABLE 
    pendingMessages
messageVars == <<messages, pendingMessages>>

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE 
    \* @type: Int -> Int;
    currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE 
    \* @type: Int -> Str;
    state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE 
    \* @type: Int -> Int;
    votedFor
serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE 
    \* @type: Int -> LOGT;
    log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE 
    \* @type: Int -> Int;
    commitIndex
logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE 
    \* @type: Int -> Set(Int);
    votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE 
    \* @type: Int -> Set(Int);
    votesGranted
\* @type: Seq(Int -> Set(Int));
candidateVars == <<votesResponded, votesGranted>>

\* The following variables are used only on leaders:
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE 
    \* @type: Int -> (Int -> Int);
    matchIndex
VARIABLE
    pendingConfChangeIndex
leaderVars == <<matchIndex, pendingConfChangeIndex>>

VARIABLE 
    config

VARIABLE 
    durableState

currentDurableState == 
    [ 
        currentTerm |-> currentTerm,
        votedFor |-> votedFor,
        log |-> log,
        commitIndex |-> commitIndex,
        config |-> config
    ]


\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messageVars, serverVars, candidateVars, leaderVars, logVars, config, durableState>>
systemState == [
    \* messageVars
    messages |-> messages,
    pendingMessages |-> pendingMessages,
    \* serverVars
    currentTerm |-> currentTerm,
    state |-> state,
    votedFor |-> votedFor,
    \* candidateVars
    votesResponded |-> votesResponded,
    votesGranted |-> votesGranted,
    \* leaderVars
    matchIndex |-> matchIndex,
    pendingConfChangeIndex |-> pendingConfChangeIndex,
    \* logVars
    log |-> log,
    commitIndex |-> commitIndex,
    \* config
    config |->config
]


----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(c) == {i \in SUBSET(c) : Cardinality(i) * 2 > Cardinality(c)}

\* The term of the last entry in a log, or 0 if the log is empty.
\* @type: LOGT => Int;
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
\* @type: (MSG, MSG -> Int) => MSG -> Int;
WithMessage(m, msgs) == msgs (+) SetToBag({m})

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
\* @type: (MSG, MSG -> Int) => MSG -> Int;
WithoutMessage(m, msgs) == msgs (-) SetToBag({m})

\* @type: a => MSG;
WrapMsg(m) == 
    IF "wrapped" \notin DOMAIN m THEN
        IF m.mtype = RequestVoteRequest THEN
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> m, RVResp |-> EmptyRVRespMsg, AEReq |-> EmptyAEReqMsg, AEResp |-> EmptyAERespMsg ]
        ELSE IF m.mtype = RequestVoteResponse THEN
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> EmptyRVReqMsg, RVResp |-> m, AEReq |-> EmptyAEReqMsg, AEResp |-> EmptyAERespMsg ]
        ELSE IF m.mtype = AppendEntriesRequest THEN
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> EmptyRVReqMsg, RVResp |-> EmptyRVRespMsg, AEReq |-> m, AEResp |-> EmptyAERespMsg ]
        ELSE
            [ wrapped |-> TRUE, mtype |-> m.mtype, mterm |-> m.mterm, msource |-> m.msource, mdest |-> m.mdest, RVReq |-> EmptyRVReqMsg, RVResp |-> EmptyRVRespMsg, AEReq |-> EmptyAEReqMsg, AEResp |-> m ]
    ELSE m

\* Add a message to the bag of pendingMessages.
SendDirect(m) == 
    pendingMessages' = WithMessage(m, pendingMessages)

\* Move all messages in pendingMessages to messages
SendPendingMessages ==
    /\ messages' = pendingMessages (+) messages
    /\ pendingMessages' = EmptyBag

\* Remove a message from the bag of messages. Used when a server is done
DiscardDirect(m) ==
    messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
ReplyDirect(response, request) ==
    /\ pendingMessages' = WithMessage(response, pendingMessages)
    /\ messages' = WithoutMessage(request, messages)

\* Default: change when needed
 Send(m) == SendDirect(m)
 Reply(response, request) == ReplyDirect(response, request)
 Discard(m) == DiscardDirect(m)

MaxOrZero(s) == IF s = {} THEN 0 ELSE Max(s)

GetJointConfig(i) == 
    config[i]

GetConfig(i) == 
    GetJointConfig(i)[1]

GetOutgoingConfig(i) ==
    GetJointConfig(i)[2]

IsJointConfig(i) ==
    /\ config[i][2] # {}

CurrentLeaders == {i \in Server : state[i] = Leader}

----
\* Define initial values for all variables
InitMessageVars == /\ messages = EmptyBag
                   /\ pendingMessages = EmptyBag
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
InitLeaderVars == /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
                  /\ pendingConfChangeIndex = [i \in Server |-> 0]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
InitConfig == /\ config = [ i \in Server |-> <<Server, {}>> ]
InitDurableState == 
    durableState = currentDurableState

Init == /\ InitMessageVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitConfig
        /\ InitDurableState

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, commitIndex, votedFor, log, and config in durable state.
\* @type: Int => Bool;
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = 0]
    /\ pendingMessages' = EmptyBag
    /\ currentTerm' = [currentTerm EXCEPT ![i] = durableState.currentTerm[i]]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = durableState.commitIndex[i]]
    /\ votedFor' = [votedFor EXCEPT ![i] = durableState.votedFor[i]]
    /\ log' = [log EXCEPT ![i] = durableState.log[i]]
    /\ config' = [config EXCEPT ![i] = durableState.config[i]]
    /\ UNCHANGED <<messages, durableState>>

\* Server i times out and starts a new election.
\* @type: Int => Bool;
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ i \in GetConfig(i)
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              /\ votedFor' = [votedFor EXCEPT ![i] = i]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ UNCHANGED <<messageVars, leaderVars, logVars, config, durableState>>

\* Candidate i sends j a RequestVote request.
\* @type: (Int, Int) => Bool;
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \in (GetConfig(i) \ votesResponded[i])
    /\ IF i # j 
        THEN Send([mtype            |-> RequestVoteRequest,
                   mterm            |-> currentTerm[i],
                   mlastLogTerm     |-> LastTerm(log[i]),
                   mlastLogIndex    |-> Len(log[i]),
                   msource          |-> i,
                   mdest            |-> j])
        ELSE Send([mtype            |-> RequestVoteResponse,
                   mterm            |-> currentTerm[i],
                   mvoteGranted     |-> TRUE,
                   mlog             |-> log[i],
                   msource          |-> i,
                   mdest            |-> i])
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, config, durableState>>

\* Leader i sends j an AppendEntries request containing entries in [b,e) range.
\* N.B. range is right open
\* @type: (Int, Int, <<Int, Int>>, Int) => Bool;
AppendEntriesInRange(subtype, i, j, range) ==
    /\ range[1] <= range[2]
    /\ state[i] = Leader
    /\ j \in GetConfig(i)
    /\ IF i /= j THEN
        /\ LET prevLogIndex == range[1] - 1
            \* The following upper bound on prevLogIndex is unnecessary
            \* but makes verification substantially simpler.
            prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[i]) THEN
                                log[i][prevLogIndex].term
                            ELSE
                                0
            \* Send the entries
            lastEntry == Min({Len(log[i]), range[2]-1})
            entries == SubSeq(log[i], range[1], lastEntry)
            commit == IF subtype = "heartbeat" THEN Min({commitIndex[i], matchIndex[i][j]}) ELSE Min({commitIndex[i], lastEntry})
            IN /\ Send([mtype          |-> AppendEntriesRequest,
                        msubtype       |-> subtype,
                        mterm          |-> currentTerm[i],
                        mprevLogIndex  |-> prevLogIndex,
                        mprevLogTerm   |-> prevLogTerm,
                        mentries       |-> entries,
                        mcommitIndex   |-> commit,
                        msource        |-> i,
                        mdest          |-> j])
               /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, config, durableState>> 
       ELSE \* etcd leader sends MsgAppResp to itself immediately after appending log entry 
        /\ Send([mtype           |-> AppendEntriesResponse,
                 mterm           |-> currentTerm[i],
                 msuccess        |-> TRUE,
                 mmatchIndex     |-> Len(log[i]),
                 msource         |-> i,
                 mdest           |-> i])
        /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, config, durableState>>

AppendEntries(i, j, range) ==
    AppendEntriesInRange("app", i, j, range)

Heartbeat(i, j) ==
    AppendEntriesInRange("heartbeat", i, j, <<1,1>>)

SendSnapshot(i, j, index) ==
    AppendEntriesInRange("snapshot", i, j, <<1,index+1>>)
    
\* Candidate i transitions to leader.
\* @type: Int => Bool;
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum(GetConfig(i))
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> IF j = i THEN Len(log[i]) ELSE 0]]
    /\ UNCHANGED <<messageVars, currentTerm, votedFor, pendingConfChangeIndex, candidateVars, logVars, config, durableState>>
    
Replicate(i, v, t) == 
    /\ t \in {ValueEntry, ConfigEntry}
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i],
                     type  |-> t,
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]

\* Leader i receives a client request to add v to the log.
\* @type: (Int, Int) => Bool;
ClientRequest(i, v) ==
    /\ Replicate(i, v, ValueEntry)
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, commitIndex, config, durableState>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\* @type: Int => Bool;
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {k \in GetConfig(i) : matchIndex[i][k] >= index}
           logSize == Len(log[i])
           \* logSize == MaxLogLength
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..logSize :
                                Agree(index) \in Quorum(GetConfig(i))}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
            committed == newCommitIndex > commitIndex[i]
       IN
        /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, leaderVars, log, config, durableState>>

    
\* Leader i adds a new server j to the cluster.
AddNewServer(i, j) ==
    /\ state[i] = Leader
    /\ j \notin GetConfig(i)
    /\ pendingConfChangeIndex[i] = 0
    /\ ~IsJointConfig(i)
    /\ Replicate(i, [newconf |-> GetConfig(i) \union {j}], ConfigEntry)
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=Len(log'[i])]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, config, durableState>>

\* Leader i removes a server j (possibly itself) from the cluster.
DeleteServer(i, j) ==
    /\ state[i] = Leader
    /\ state[j] \in {Follower, Candidate}
    /\ j \in GetConfig(i)
    /\ pendingConfChangeIndex[i] = 0
    /\ ~IsJointConfig(i)
    /\ Replicate(i, [newconf |-> GetConfig(i) \ {j}], ConfigEntry)
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i]=Len(log'[i])]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, commitIndex, config, durableState>>

ApplySimpleConfChangeInLeader(i) ==
    /\ state[i] = Leader
    /\ pendingConfChangeIndex[i] > 0
    /\ pendingConfChangeIndex[i] <= commitIndex[i]
    /\ ~IsJointConfig(i)
    /\ IF log[i][pendingConfChangeIndex[i]].type = ConfigEntry THEN
            config' = [config EXCEPT ![i]= << log[i][pendingConfChangeIndex[i]].value.newconf, {} >>]
       ELSE 
            UNCHANGED <<config>>
    /\ pendingConfChangeIndex' = [pendingConfChangeIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messageVars, serverVars, candidateVars, matchIndex, logVars, durableState>>
    
Ready(i) ==
    /\ durableState' = currentDurableState
    \* In etcd, candidate or follower needs to wait for all pending configuration changes to be applied before sending messages.
    /\ \/ /\ state[i] \in {Follower, Candidate}
          /\ LET k == SelectLastInSubSeq(log[i], 1, commitIndex[i], LAMBDA x: x.type = ConfigEntry)
             IN IF k > 0 THEN 
                    config' = [config EXCEPT ![i] = << log[i][k].value.newconf, {} >>]
                ELSE
                    UNCHANGED <<config>>
       \/ /\ state[i] = Leader
          /\ UNCHANGED <<config>>
    /\ SendPendingMessages
    /\ UNCHANGED <<serverVars, leaderVars, candidateVars, logVars>>

BecomeFollowerOfTerm(i, t) ==
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = t]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ IF currentTerm[i] # t THEN  
            votedFor' = [votedFor    EXCEPT ![i] = Nil]
       ELSE 
            UNCHANGED <<votedFor>>

StepDownToFollower(i) ==
    /\ state[i] \in {Leader, Candidate}
    /\ BecomeFollowerOfTerm(i, currentTerm[i])
    /\ UNCHANGED <<messageVars, candidateVars, leaderVars, logVars, config, durableState>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* @type: (Int, Int, RVREQT) => Bool;
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, config, durableState>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
\* @type: (Int, Int, RVRESPT) => Bool;
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted>>
    /\ Discard(m)
    /\ UNCHANGED <<pendingMessages, serverVars, votedFor, leaderVars, logVars, config, durableState>>

\* @type: (Int, Int, AEREQT, Bool) => Bool;
RejectAppendEntriesRequest(i, j, m, logOk) ==
    /\ \/ m.mterm < currentTerm[i]
       \/ /\ m.mterm = currentTerm[i]
          /\ state[i] = Follower
          /\ \lnot logOk
    /\ Reply([mtype           |-> AppendEntriesResponse,
              mterm           |-> currentTerm[i],
              msuccess        |-> FALSE,
              mmatchIndex     |-> 0,
              msource         |-> i,
              mdest           |-> j],
              m)
    /\ UNCHANGED <<serverVars, logVars, config, durableState>>

\* @type: (Int, MSG) => Bool;
ReturnToFollowerState(i, m) ==
    /\ m.mterm = currentTerm[i]
    /\ state[i] = Candidate
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ UNCHANGED <<messageVars, currentTerm, votedFor, logVars, config, durableState>> 

HasNoConflict(i, index, ents) ==
    /\ index <= Len(log[i]) + 1
    /\ \A k \in 1..Len(ents): index + k - 1 <= Len(log[i]) => log[i][index+k-1].term = ents[k].term

\* @type: (Int, Int, Int, AEREQT) => Bool;
AppendEntriesAlreadyDone(i, j, index, m) ==
    /\ \/ index <= commitIndex[i]
       \/ m.mentries = << >>
       \/ /\ m.mentries /= << >>
          /\ m.mprevLogIndex + Len(m.mentries) <= Len(log[i])
          /\ HasNoConflict(i, index, m.mentries)          
    /\ commitIndex' = [commitIndex EXCEPT ![i] = IF index <= commitIndex[i] THEN @ ELSE Min({m.mcommitIndex, m.mprevLogIndex+Len(m.mentries)})]
    /\ Reply([  mtype           |-> AppendEntriesResponse,
                msubtype        |-> m.msubtype,
                mterm           |-> currentTerm[i],
                msuccess        |-> TRUE,
                mmatchIndex     |-> IF m.msubtype = "heartbeat" \/ index > commitIndex[i] THEN m.mprevLogIndex+Len(m.mentries) ELSE commitIndex[i],
                msource         |-> i,
                mdest           |-> j],
                m)
    /\ UNCHANGED <<serverVars, log, config, durableState>>

\* @type: (Int, Int, AEREQT) => Bool;
ConflictAppendEntriesRequest(i, index, m) ==
    /\ m.mentries /= << >>
    /\ index > commitIndex[i]
    /\ ~HasNoConflict(i, index, m.mentries)
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i]) - 1)]
    /\ UNCHANGED <<messageVars, serverVars, commitIndex, durableState>>

\* @type: (Int, AEREQT) => Bool;
NoConflictAppendEntriesRequest(i, index, m) ==
    /\ m.mentries /= << >>
    /\ HasNoConflict(i, index, m.mentries)
    /\ log' = [log EXCEPT ![i] = @ \o SubSeq(m.mentries, Len(log[i])-index+2, Len(m.mentries))]
    /\ UNCHANGED <<messageVars, serverVars, commitIndex, durableState>>

\* @type: (Int, Int, Bool, AEREQT) => Bool;
AcceptAppendEntriesRequest(i, j, logOk, m) ==
    \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ AppendEntriesAlreadyDone(i, j, index, m)
                   \/ ConflictAppendEntriesRequest(i, index, m)
                   \/ NoConflictAppendEntriesRequest(i, index, m)

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
\* @type: (Int, Int, AEREQT) => Bool;
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN 
       /\ m.mterm <= currentTerm[i]
       /\ \/ RejectAppendEntriesRequest(i, j, m, logOk)
          \/ ReturnToFollowerState(i, m)
          \/ AcceptAppendEntriesRequest(i, j, logOk, m)
       /\ UNCHANGED <<candidateVars, leaderVars, config, durableState>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
\* @type: (Int, Int, AERESPT) => Bool;
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = Max({@, m.mmatchIndex})]
          /\ UNCHANGED <<pendingConfChangeIndex>>
       \/ /\ \lnot m.msuccess \* not successful
          /\ UNCHANGED <<leaderVars>>
    /\ Discard(m)
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, logVars, config, durableState>>

\* Any RPC with a newer term causes the recipient to advance its term first.
\* @type: (Int, Int, MSG) => Bool;
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ BecomeFollowerOfTerm(i, m.mterm)
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messageVars, candidateVars, leaderVars, logVars, config, durableState>>

\* Responses with stale terms are ignored.
\* @type: (Int, Int, MSG) => Bool;
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, leaderVars, logVars, config, durableState>>

\* Receive a message.
ReceiveDirect(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
    \/ UpdateTerm(i, j, m)
    \/  /\ m.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(i, j, m)
    \/  /\ m.mtype = RequestVoteResponse
        /\  \/ DropStaleResponse(i, j, m)
            \/ HandleRequestVoteResponse(i, j, m)
    \/  /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m)
    \/  /\ m.mtype = AppendEntriesResponse
        /\  \/ DropStaleResponse(i, j, m)
            \/ HandleAppendEntriesResponse(i, j, m)

\* @type: MSG => Bool;
ReceiveWrapped(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
    \/ UpdateTerm(i, j, m)
    \/  /\ m.mtype = RequestVoteRequest
        /\ HandleRequestVoteRequest(i, j, m.RVReq)
    \/  /\ m.mtype = RequestVoteResponse
        /\  \/ DropStaleResponse(i, j, m.RVResp)
            \/ HandleRequestVoteResponse(i, j, m.RVResp)
    \/  /\ m.mtype = AppendEntriesRequest
        /\ HandleAppendEntriesRequest(i, j, m.AEReq)
    \/  /\ m.mtype = AppendEntriesResponse
        /\  \/ DropStaleResponse(i, j, m.AEResp)
            \/ HandleAppendEntriesResponse(i, j, m.AEResp)

 Receive(m) == ReceiveDirect(m)
\*Receive(m) == ReceiveWrapped(m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
\* @type: MSG => Bool;
DuplicateMessage(m) ==
    /\ m \in DOMAIN messages
    /\ messages' = WithMessage(m, messages)
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, leaderVars, logVars, config, durableState>>

\* The network drops a message
\* @type: MSG => Bool;
DropMessage(m) ==
    \* Do not drop loopback messages
    \* /\ m.msource /= m.mdest
    /\ Discard(m)
    /\ UNCHANGED <<pendingMessages, serverVars, candidateVars, leaderVars, logVars, config, durableState>>

----

\* Defines how the variables may transition.
NextAsync == 
    \/ \E i,j \in Server : RequestVote(i, j)
    \/ \E i \in Server : BecomeLeader(i)
    \/ \E i \in Server: ClientRequest(i, 0)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i,j \in Server : \E b,e \in matchIndex[i][j]+1..Len(log[i])+1 : AppendEntries(i, j, <<b,e>>)
    \/ \E i,j \in Server : Heartbeat(i, j)
    \/ \E i,j \in Server : \E index \in 1..commitIndex[i] : SendSnapshot(i, j, index)
    \/ \E m \in DOMAIN messages : Receive(m)
    \/ \E i \in Server : Timeout(i)
    \/ \E i \in Server : Ready(i)
    \/ \E i \in Server : StepDownToFollower(i)
        
NextCrash == \E i \in Server : Restart(i)

NextAsyncCrash ==
    \/ NextAsync
    \/ NextCrash

NextUnreliable ==    
    \* Only duplicate once
    \/ \E m \in DOMAIN messages : 
        /\ messages[m] = 1
        /\ DuplicateMessage(m)
    \* Only drop if it makes a difference            
    \/ \E m \in DOMAIN messages : 
        /\ messages[m] = 1
        /\ DropMessage(m)

\* Most pessimistic network model
Next == \/ NextAsync
        \/ NextCrash
        \/ NextUnreliable

\* Membership changes
NextDynamic ==
    \/ Next
    \/ \E i, j \in Server : AddNewServer(i, j)
    \/ \E i, j \in Server : DeleteServer(i, j)
    \/ \E i \in Server : ApplySimpleConfChangeInLeader(i)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The main safety properties are below                                    *)
(***************************************************************************)
----

ASSUME DistinctRoles == /\ Leader /= Candidate
                        /\ Candidate /= Follower
                        /\ Follower /= Leader

ASSUME DistinctMessageTypes == /\ RequestVoteRequest /= AppendEntriesRequest
                               /\ RequestVoteRequest /= RequestVoteResponse
                               /\ RequestVoteRequest /= AppendEntriesResponse
                               /\ AppendEntriesRequest /= RequestVoteResponse
                               /\ AppendEntriesRequest /= AppendEntriesResponse
                               /\ RequestVoteResponse /= AppendEntriesResponse

----
\* Correctness invariants

\* The prefix of the log of server i that has been committed
Committed(i) == SubSeq(log[i],1,commitIndex[i])

\* The current term of any server is at least the term
\* of any message sent by that server
\* @type: MSG => Bool;
MessageTermsLtCurrentTerm(m) ==
    m.mterm <= currentTerm[m.msource]

----
\* I believe that the election safety property in the Raft
\* paper is stronger than it needs to be and requires history
\* variables. The definition ElectionSafety is an invariant that
\* is strong enough without requiring history variables. First,
\* we state two properties which will allow us to conclude election
\* safety
    
\* NOTE: this only makes sense if there are no configuration changes
\* All leaders have a quorum of servers who either voted
\* for the leader or have a higher term
(* LeaderVotesQuorum ==
    history["hadNumMembershipChanges"] = 0 =>
    \A i \in Server :
        state[i] = Leader =>
        {j \in Server : currentTerm[j] > currentTerm[i] \/
                        (currentTerm[j] = currentTerm[i] /\ votedFor[j] = i)} \in Quorum(GetConfig(i))

\* If a candidate has a chance of being elected, there
\* are no log entries with that candidate's term
CandidateTermNotInLog ==
    history["hadNumMembershipChanges"] = 0 =>
    \A i \in Server :
        (/\ state[i] = Candidate
         /\ {j \in Server : currentTerm[j] = currentTerm[i] /\ votedFor[j] \in {i, Nil}} \in Quorum(GetConfig(i))) =>
        \A j \in Server :
        \A n \in DOMAIN log[j] :
             log[j][n].term /= currentTerm[i]

THEOREM ElectionsCorrect == Spec => [](CandidateTermNotInLog /\ LeaderVotesQuorum)
 *)
\* A leader always has the greatest index for its current term
ElectionSafety ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            MaxOrZero({n \in DOMAIN log[i] : log[i][n].term = currentTerm[i]}) >=
            MaxOrZero({n \in DOMAIN log[j] : log[j][n].term = currentTerm[i]})
----
\* Every (index, term) pair determines a log prefix
LogMatching ==
    \A i, j \in Server :
        \A n \in (1..Len(log[i])) \cap (1..Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)
----
\* A leader has all committed entries in its log. This is expressed
\* by LeaderCompleteness below. The inductive invariant for
\* that property is the conjunction of LeaderCompleteness with the
\* other three properties below.

\* This property, written by Daniel Ricketts, is in fact
\* violated. This suggests the spec was not model-checked
\* extensively.

\* The English description is correct, but the TLA
\* does NOT match it due to a confusion about the meaning
\* of the spec variables.

\* Votes are only granted to servers with logs
\* that are at least as up to date
VotesGrantedInv_false ==
    \A i \in Server :
    \A j \in votesGranted[i] :
        currentTerm[i] = currentTerm[j] =>
        \* The following is a subtlety:
        \* Only the committed entries of j are
        \* a prefix of i's log, not the entire 
        \* log of j
        IsPrefix(Committed(j),log[i])

VotesGrantedInv ==
    \A i, j \in Server :
        \* if i has voted for j
        votedFor[i] = j =>
            IsPrefix(Committed(i), log[j])

\* All committed entries are contained in the log
\* of at least one server in every quorum
QuorumLogInv ==
    \A i \in Server :
    \A S \in Quorum(GetConfig(i)) :
        \E j \in S :
            IsPrefix(Committed(i), log[j])

\* The "up-to-date" check performed by servers
\* before issuing a vote implies that i receives
\* a vote from j only if i has all of j's committed
\* entries
MoreUpToDateCorrect ==
    \A i, j \in Server :
       (\/ LastTerm(log[i]) > LastTerm(log[j])
        \/ /\ LastTerm(log[i]) = LastTerm(log[j])
           /\ Len(log[i]) >= Len(log[j])) =>
       IsPrefix(Committed(j), log[i])

\* This property, written by Daniel Rickett's, is in fact
\* violated by the spec (when there are multiple concurrent leaders).
\*  This suggests the spec was not model-checked extensively.

\* The committed entries in every log are a prefix of the
\* leader's log
LeaderCompleteness_false ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server :
            IsPrefix(Committed(j),log[i])

\* If a log entry is committed in a given term, then that
\* entry will be present in the logs of the leaders
\* for all higher-numbered terms
\* See: https://github.com/uwplse/verdi-raft/blob/master/raft/LeaderCompletenessInterface.v
LeaderCompleteness == 
    \A i \in Server :
        LET committed == Committed(i) IN
        \A idx \in 1..Len(committed) :
            LET entry == log[i][idx] IN 
            \* if the entry is committed 
            \A l \in CurrentLeaders :
                \* all leaders with higher-number terms
                currentTerm[l] > entry.term =>
                \* have the entry at the same log position
                log[l][idx] = entry

-----


===============================================================================



\* Changelog:
\*  
\* 2021-04-??:
\* - Abandoned Apalache due to slowness and went back to TLC. There are remains
\*   of the Apalache-specific annotations and message wrapping/unwrapping, but
\*   those are not actually used. The annotations are no longer up-to-date. 
\*
\* 2021-04-09:
\* - Added type annotations for Apalache symbolic model checker. As part of
\*   this change, the message format was changed to a tagged union.
\* 
\* 2016-09-09:
\* - Daniel Ricketts added the major safety invariants and proved them in
\*   TLAPS.
\*
\* 2015-05-10:
\* - Add cluster membership changes as described in Section 4 of
\*     Diego Ongaro. Consensus: Bridging theory and practice.
\*     PhD thesis, Stanford University, 2014.
\*   This introduces: InitServer, ValueEntry, ConfigEntry, CatchupRequest,
\*     CatchupResponse, CheckOldConfig, GetMaxConfigIndex,
\*     GetConfig (parameterized), AddNewServer, DeleteServer,
\*     HandleCatchupRequest, HandleCatchupResponse,
\*     HandleCheckOldConfig 
\*
\* 
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
