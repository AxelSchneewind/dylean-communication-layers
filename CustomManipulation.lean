module

import Init.Control.Lawful.Basic
public import Lean
public import DY.Trace.Basic
public import DY.Trace.Monad
public import DY.Trace.Reachability
public import DY.Trace.Invariant
public import DY.Trace.Manipulation

namespace DY

-- wrapper around getEntry with stronger postcondition
-- TODO: find a better solution
public
def getEntryStronger
  [ExecTraceTypes] {EntryT: Type} [ExecTraceTypes.Has EntryT]
  (timestamp: Nat)
  : Traceful EntryT
:=
  Traceful.mk (fun tr =>
    let result := tr.at? timestamp
    (result, ⟨ tr, by grind ⟩ )
  )

@[instance]
public
theorem getEntryStronger.spec
  [ExecTraceTypes] [ProofTraceTypes] [TraceInvariant]
  {ExecEntryT ProofEntryT: Type}
  [ExecEntryAssociatedWithProofEntry ExecEntryT ProofEntryT]
  [ErasableProofEntry ExecEntryT ProofEntryT]
  [SubTraceInvariant ProofEntryT]
  [ExecTraceTypes.Has ExecEntryT]
  [ProofTraceTypes.Has ProofEntryT]
  [TraceInvariant.Has ProofEntryT]
  (timestamp: Nat)
  : HoareTriple
    (getEntryStronger timestamp: Traceful ExecEntryT)
    (fun _ => True)
    (fun entry tr =>
      ∃ proofEntry: ProofEntryT,
      entry = ErasableProofEntry.erase proofEntry ∧
      SubTraceInvariant.invariant (tr.prefix timestamp) proofEntry ∧
      tr.at? timestamp = some proofEntry
    )
:= by
  apply HoareTriple.mk
  simp only [hoareTriple, wp, getEntryStronger, Traceful.run_mk]
  intro trProof h_pre h_inv
  exists trProof
  split
  · grind
  simp only [h_inv, Trace.le_refl, and_true]
  rename_i trProof execEntry heq
  cases h: (tr_proof'.at? timestamp: Option ProofEntryT)
  · simp_all [ProofTrace.Entry.at?_eq_none_erase]
  rename_i proofEntry
  exists proofEntry
  have := ProofTrace.Entry.at?_eq_some_erase tr_proof' timestamp proofEntry h
  constructor
  · grind
  rewrite [← TraceInvariant.Has.inv_commutes]
  grind [Trace.at?_eq_some, Trace.invariant_at]


public
theorem getEntryStronger.preservesReachability
  [ExecTraceTypes]
  {ExecEntryT: Type}
  [ExecTraceTypes.Has ExecEntryT]
  (config: ReachabilityConfig)
  (timestamp: Nat)
  : Traceful.PreservesReachability config
    (getEntryStronger timestamp: Traceful ExecEntryT)
    (fun _ => True)
    (fun entry tr => tr.at? timestamp = some entry)
:= by
  simp only [Traceful.PreservesReachability, Traceful.PreservesReachabilityFrom, getEntryStronger, Traceful.run_mk]
  grind
