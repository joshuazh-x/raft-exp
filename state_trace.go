package raft

import (
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
	RsmSendAppendEntriesRequest
	RsmReceiveAppendEntriesRequest
	RsmSendAppendEntriesResponse
	RsmReceiveAppendEntriesResponse
	RsmSendRequestVoteRequest
	RsmReceiveRequestVoteRequest
	RsmSendRequestVoteResponse
	RsmReceiveRequestVoteResponse
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
		"SendAppendEntriesRequest",
		"ReceiveAppendEntriesRequest",
		"SendAppendEntriesResponse",
		"ReceiveAppendEntriesResponse",
		"SendRequestVoteRequest",
		"ReceiveRequestVoteRequest",
		"SendRequestVoteResponse",
		"ReceiveRequestVoteResponse",
	}[e]
}

const (
	ConfChangeAddNewServer string = "AddNewServer"
	ConfChangeRemoveServer string = "RemoveServer"
)

type TracingEvent struct {
	Name       string             `json:"name"`
	NodeID     uint64             `json:"nid"`
	State      raftpb.HardState   `json:"state"`
	Role       string             `json:"role"`
	Conf       [2][]uint64        `json:"conf"`
	Message    *TracingMessage    `json:"msg,omitempty"`
	ConfChange *TracingConfChange `json:"cc,omitempty"`
}

type TracingMessage struct {
	Type        string `json:"type"`
	Term        uint64 `json:"term"`
	From        uint64 `json:"from"`
	To          uint64 `json:"to"`
	EntryLength int    `json:"entries"`
	LogTerm     uint64 `json:"logTerm"`
	Index       uint64 `json:"index"`
	Commit      uint64 `json:"commit"`
	Vote        uint64 `json:"vote"`
	Reject      bool   `json:"reject"`
	RejectHint  uint64 `json:"rejectHint"`
}

type SingleConfChange struct {
	NodeId uint64 `json:"nid"`
	Action string `json:"action"`
}

type TracingConfChange struct {
	Changes []SingleConfChange `json:"changes,omitempty"`
	NewConf []uint64           `json:"newconf,omitempty"`
}

func makeTracingMessage(m *raftpb.Message) *TracingMessage {
	if m == nil {
		return nil
	}

	return &TracingMessage{
		Type:        m.Type.String(),
		Term:        m.Term,
		From:        m.From,
		To:          m.To,
		EntryLength: len(m.Entries),
		LogTerm:     m.LogTerm,
		Index:       m.Index,
		Commit:      m.Commit,
		Vote:        m.Vote,
		Reject:      m.Reject,
		RejectHint:  m.RejectHint,
	}
}

type RaftStateMachineTracer interface {
	TraceState(*TracingEvent)
}

var stateTracer RaftStateMachineTracer

func SetStateTracer(t RaftStateMachineTracer) {
	stateTracer = t
}

func traceEvent(evt RaftStateMachineEventType, r *raft, m *raftpb.Message, cc *TracingConfChange) {
	if stateTracer == nil {
		return
	}

	stateTracer.TraceState(&TracingEvent{
		Name:       evt.String(),
		NodeID:     r.id,
		State:      r.hardState(),
		Conf:       [2][]uint64{nonNilSlice(r.prs.Voters[0].Slice()), nonNilSlice(r.prs.Voters[1].Slice())},
		Role:       r.state.String(),
		Message:    makeTracingMessage(m),
		ConfChange: cc,
	})
}

func traceNodeEvent(evt RaftStateMachineEventType, r *raft) {
	traceEvent(evt, r, nil, nil)
}

func traceChangeConfEvent(cci raftpb.ConfChangeI, r *raft) {
	cc2 := cci.AsV2()
	cc := &TracingConfChange{
		Changes: []SingleConfChange{},
		NewConf: []uint64{},
	}
	for _, c := range cc2.Changes {
		switch c.Type {
		case raftpb.ConfChangeAddNode:
			cc.Changes = append(cc.Changes, SingleConfChange{
				NodeId: c.NodeID,
				Action: ConfChangeAddNewServer,
			})
		case raftpb.ConfChangeRemoveNode:
			cc.Changes = append(cc.Changes, SingleConfChange{
				NodeId: c.NodeID,
				Action: ConfChangeRemoveServer,
			})
		}
	}

	traceEvent(RsmChangeConf, r, nil, cc)
}

func traceConfChangeEvent(cfg tracker.Config, r *raft) {
	if stateTracer == nil {
		return
	}

	cc := &TracingConfChange{
		Changes: []SingleConfChange{},
		NewConf: nonNilSlice(cfg.Voters[0].Slice()),
	}

	traceEvent(RsmApplyConfChange, r, nil, cc)
}

func traceSendMessage(r *raft, m *raftpb.Message) {
	if stateTracer == nil {
		return
	}

	var evt RaftStateMachineEventType
	switch m.Type {
	case raftpb.MsgApp:
		evt = RsmSendAppendEntriesRequest
	case raftpb.MsgAppResp:
		evt = RsmSendAppendEntriesResponse
	case raftpb.MsgVote:
		evt = RsmSendRequestVoteRequest
	case raftpb.MsgVoteResp:
		evt = RsmSendRequestVoteResponse
	default:
		return
	}

	traceEvent(evt, r, m, nil)
}

func traceReceiveMessage(r *raft, m *raftpb.Message) {
	if stateTracer == nil {
		return
	}

	var evt RaftStateMachineEventType
	switch m.Type {
	case raftpb.MsgApp:
		evt = RsmReceiveAppendEntriesRequest
	case raftpb.MsgAppResp:
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

func nonNilSlice(s []uint64) []uint64 {
	if s == nil {
		return []uint64{}
	}

	return s
}
