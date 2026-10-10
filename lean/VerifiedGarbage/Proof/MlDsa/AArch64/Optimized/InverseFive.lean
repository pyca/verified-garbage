import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedTable

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def fiveCode : List Instr := packedCode packedSteps ++ runCode (localPlan 0).load 0 7

def fiveValues (u : Nat) (v : Vector (BitVec 128) 8) : Vector (BitVec 128) 8 :=
  runValues (localRoot u) 0 7 (packedRunValues v (packedRoot u) packedSteps)

/-- A table plan's loads do not depend on its roots. Stated for any roots: checking
`(localPlan u).load = (localPlan 0).load` by `rfl` first compares the roots,
unfolding the modular arithmetic of the table for seconds before it fails. -/
theorem tablePlan_load {offset : Nat → Nat} {z z' : Nat → Nat → Int} {ha hi hz hz'} :
    (tablePlan offset z ha hi hz).load = (tablePlan offset z' ha hi hz').load := rfl

theorem five_ok (u : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} (hb : Bank s (regs 0) v)
    (hp : PackedRoots s (packedRoot u)) (hl : TableRoots localOffset (localRoot u) s)
    (k : ∀ t, VChg runRegs s t → Bank t (regs 7) (fiveValues u v) → WP isa (.block rest) t Q) :
    WP isa (.block (fiveCode ++ rest)) s Q := by
  unfold fiveCode
  rw [List.append_assoc]
  refine packedRun_ok packedSteps packedSteps_valid hb hp fun s₁ hc₁ _ hb₁ => ?_
  have hl₁ := hl.frame hc₁ (by decide)
  have code_eq : runCode (localPlan u).load 0 7=runCode (localPlan 0).load 0 7 :=
    congrArg (fun l => runCode l 0 7) tablePlan_load
  rw [← code_eq]
  refine run_ok (localPlan u) 0 7 (by decide) hb₁ hl₁ fun t hc₂ _ hb₂ => ?_
  refine k t (VChg.mono (hc₁.trans hc₂) ?_) hb₂
  intro r h
  rcases List.mem_append.mp h with h | h
  · exact (show packedRegs⊆runRegs by decide) h
  · exact h

def firstLoads : List Instr := (List.range 8).map fun j => Instr.ldrq (VG.Impl.MlDsa.AArch64.Optimized.Inverse.vr j) .x0 (16*j)
def firstStores : List Instr := (List.finRange 8).map fun j => Instr.strq (regs 7)[j.val] .x0 (16*j.val)
def firstAdvance : List Instr := [.addImm .x .x0 .x0 128,.addImm .x .x1 .x1 480,.subImm .x .x11 .x11 1]

theorem firstBlock_eq : VG.Impl.MlDsa.AArch64.Optimized.Inverse.firstBlock=
    firstLoads ++ fiveCode ++ firstStores ++ firstAdvance := by decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
