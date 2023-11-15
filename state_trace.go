package raft

import (
	"strconv"

	"go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

type RaftStateMachineEventType int

const (
	RsmInitState RaftStateMachineEventType = iota
	RsmBecomeCandidate
	RsmBecomeFollower
	RsmBecomeLeader
	RsmCommit
	RsmReplicate
	RsmChangeConf
	RsmApplyConfChange
	RsmReady
	RsmSendAppendEntriesRequest
	RsmReceiveAppendEntriesRequest
	RsmSendAppendEntriesResponse
	RsmReceiveAppendEntriesResponse
	RsmSendRequestVoteRequest
	RsmReceiveRequestVoteRequest
	RsmSendRequestVoteResponse
	RsmReceiveRequestVoteResponse
	RsmSendSnapshot
	RsmReceiveSnapshot
	RsmReduceNextIndex
)

func (e RaftStateMachineEventType) String() string {
	return []string{
		"InitState",
		"BecomeCandidate",
		"BecomeFollower",
		"BecomeLeader",
		"Commit",
		"Replicate",
		"ChangeConf",
		"ApplyConfChange",
		"Ready",
		"SendAppendEntriesRequest",
		"ReceiveAppendEntriesRequest",
		"SendAppendEntriesResponse",
		"ReceiveAppendEntriesResponse",
		"SendRequestVoteRequest",
		"ReceiveRequestVoteRequest",
		"SendRequestVoteResponse",
		"ReceiveRequestVoteResponse",
		"SendSnapshot",
		"ReceiveSnapshot",
		"ReduceNextIndex",
	}[e]
}

const (
	ConfChangeAddNewServer string = "AddNewServer"
	ConfChangeRemoveServer string = "RemoveServer"
	ConfChangeAddLearner   string = "AddLearner"
)

type TracingEvent struct {
	Name       string             `json:"name"`
	NodeID     string             `json:"nid"`
	State      TracingState       `json:"state"`
	Role       string             `json:"role"`
	LogSize    uint64             `json:"log"`
	Conf       [2][]string        `json:"conf"`
	Message    *TracingMessage    `json:"msg,omitempty"`
	ConfChange *TracingConfChange `json:"cc,omitempty"`
	Properties map[string]any     `json:"prop,omitempty"`
}

type TracingState struct {
	Term   uint64 `json:"term"`
	Vote   string `json:"vote"`
	Commit uint64 `json:"commit"`
}

type TracingMessage struct {
	Type        string `json:"type"`
	Term        uint64 `json:"term"`
	From        string `json:"from"`
	To          string `json:"to"`
	EntryLength int    `json:"entries"`
	LogTerm     uint64 `json:"logTerm"`
	Index       uint64 `json:"index"`
	Commit      uint64 `json:"commit"`
	Vote        string `json:"vote"`
	Reject      bool   `json:"reject"`
	RejectHint  uint64 `json:"rejectHint"`
}

type SingleConfChange struct {
	NodeId string `json:"nid"`
	Action string `json:"action"`
}

type TracingConfChange struct {
	Changes []SingleConfChange `json:"changes,omitempty"`
	NewConf []string           `json:"newconf,omitempty"`
}

func makeTracingState(r *raft) TracingState {
	hs := r.hardState()
	return TracingState{
		Term:   hs.Term,
		Vote:   strconv.FormatUint(hs.Vote, 10),
		Commit: hs.Commit,
	}
}

func makeTracingMessage(m *raftpb.Message) *TracingMessage {
	if m == nil {
		return nil
	}

	logTerm := m.LogTerm
	entries := len(m.Entries)
	index := m.Index
	if m.Type == raftpb.MsgSnap {
		index = 0
		logTerm = 0
		entries = int(m.Snapshot.Metadata.Index)
	}
	return &TracingMessage{
		Type:        m.Type.String(),
		Term:        m.Term,
		From:        strconv.FormatUint(m.From, 10),
		To:          strconv.FormatUint(m.To, 10),
		EntryLength: entries,
		LogTerm:     logTerm,
		Index:       index,
		Commit:      m.Commit,
		Vote:        strconv.FormatUint(m.Vote, 10),
		Reject:      m.Reject,
		RejectHint:  m.RejectHint,
	}
}

type RaftStateMachineTracer interface {
	TraceState(*TracingEvent)
}

func traceInitStateOnce(r *raft) {
	if r.stateTracer == nil {
		return
	}

	if r.initStateTraced {
		return
	}

	r.initStateTraced = true

	traceNodeEvent(RsmInitState, r)
}

func traceEvent(evt RaftStateMachineEventType, r *raft, m *raftpb.Message, prop map[string]any) {
	if r.stateTracer == nil {
		return
	}

	if !r.initStateTraced {
		return
	}

	r.stateTracer.TraceState(&TracingEvent{
		Name:       evt.String(),
		NodeID:     strconv.FormatUint(r.id, 10),
		State:      makeTracingState(r),
		LogSize:    r.raftLog.lastIndex(),
		Conf:       [2][]string{formatConf(r.prs.Voters[0].Slice()), formatConf(r.prs.Voters[1].Slice())},
		Role:       r.state.String(),
		Message:    makeTracingMessage(m),
		Properties: prop,
	})
}

func traceNodeEvent(evt RaftStateMachineEventType, r *raft) {
	traceEvent(evt, r, nil, nil)
}

func traceChangeConfEvent(cci raftpb.ConfChangeI, r *raft) {
	cc2 := cci.AsV2()
	cc := &TracingConfChange{
		Changes: []SingleConfChange{},
		NewConf: []string{},
	}
	for _, c := range cc2.Changes {
		switch c.Type {
		case raftpb.ConfChangeAddNode:
			cc.Changes = append(cc.Changes, SingleConfChange{
				NodeId: strconv.FormatUint(c.NodeID, 10),
				Action: ConfChangeAddNewServer,
			})
		case raftpb.ConfChangeRemoveNode:
			cc.Changes = append(cc.Changes, SingleConfChange{
				NodeId: strconv.FormatUint(c.NodeID, 10),
				Action: ConfChangeRemoveServer,
			})
		case raftpb.ConfChangeAddLearnerNode:
			cc.Changes = append(cc.Changes, SingleConfChange{
				NodeId: strconv.FormatUint(c.NodeID, 10),
				Action: ConfChangeAddLearner,
			})
		}
	}

	p := map[string]any{}
	p["cc"] = cc
	traceEvent(RsmChangeConf, r, nil, p)
}

func traceConfChangeEvent(cfg tracker.Config, r *raft) {
	if r.stateTracer == nil {
		return
	}

	cc := &TracingConfChange{
		Changes: []SingleConfChange{},
		NewConf: formatConf(cfg.Voters[0].Slice()),
	}

	p := map[string]any{}
	p["cc"] = cc
	traceEvent(RsmApplyConfChange, r, nil, p)
}

func traceSendMessage(r *raft, m *raftpb.Message) {
	if r.stateTracer == nil {
		return
	}

	p := map[string]any{}

	var evt RaftStateMachineEventType
	switch m.Type {
	case raftpb.MsgApp:
		evt = RsmSendAppendEntriesRequest
		p["advanceNextIndex"] = r.prs.Progress[m.To].State == tracker.StateReplicate
	case raftpb.MsgHeartbeat, raftpb.MsgSnap:
		evt = RsmSendAppendEntriesRequest
	case raftpb.MsgAppResp, raftpb.MsgHeartbeatResp:
		evt = RsmSendAppendEntriesResponse
	case raftpb.MsgVote:
		evt = RsmSendRequestVoteRequest
	case raftpb.MsgVoteResp:
		evt = RsmSendRequestVoteResponse
	default:
		return
	}

	traceEvent(evt, r, m, p)
}

func traceReceiveMessage(r *raft, m *raftpb.Message) {
	if r.stateTracer == nil {
		return
	}

	var evt RaftStateMachineEventType
	switch m.Type {
	case raftpb.MsgApp, raftpb.MsgHeartbeat, raftpb.MsgSnap:
		evt = RsmReceiveAppendEntriesRequest
	case raftpb.MsgAppResp, raftpb.MsgHeartbeatResp:
		evt = RsmReceiveAppendEntriesResponse
	case raftpb.MsgVote:
		evt = RsmReceiveRequestVoteRequest
	case raftpb.MsgVoteResp:
		evt = RsmReceiveRequestVoteResponse
	default:
		return
	}

	traceEvent(evt, r, m, nil)
}

func traceReduceNextIndex(r *raft, peer uint64) {
	if r.stateTracer == nil {
		return
	}

	p := map[string]any{}
	p["peer"] = strconv.FormatUint(peer, 10)
	p["nextIndex"] = r.prs.Progress[peer].Next
	traceEvent(RsmReduceNextIndex, r, nil, p)
}

func formatConf(s []uint64) []string {
	if s == nil {
		return []string{}
	}

	r := make([]string, len(s))
	for i, v := range s {
		r[i] = strconv.FormatUint(v, 10)
	}
	return r
}
