module

import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseLocalTable
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedRun
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots

/-! ### `MlDsa.AArch64.Optimized.InversePackedTable`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64

def packedRoot (u g len e : Nat) : Int := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z
  (if len=1 then 255-16*u-4*g-e else 127-8*u-2*g-e/2)

theorem packedRoot_range (u g len e : Nat) : 0≤packedRoot u g len e ∧ packedRoot u g len e<8380417 := by
  unfold packedRoot VG.Impl.MlDsa.AArch64.Optimized.Inverse.z
  exact ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr (Nat.mod_lt _ (by decide))⟩

theorem packed_words {m : Mem} {p : Addr} (h : InverseTable.Words m p)
    {u g len e : Nat} (hu : u<8) (hg : g<4) (hl : len=1 ∨ len=2) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+packedOffset g len)) 16) e=BitVec.ofInt 32 (packedRoot u g len e) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+packedOffset g len+16)) 16) e=
      BitVec.ofInt 32 (reciprocal (packedRoot u g len e)) := by
  rcases hl with rfl | rfl
  · simp only [packedRoot,packedOffset,ite_true,← Nat.add_assoc]
    exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (255-16*u-4*g-e))
      (h.layer1 (u := u) (g := g) (e := e) hu hg he)
  · simp only [packedRoot,packedOffset,show ¬(2=1) by decide,ite_false,← Nat.add_assoc]
    exact nat_row (n := VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (127-8*u-2*g-e/2))
      (h.layer2 (u := u) (g := g) (e := e) hu hg he)

theorem packed_tableRoots {s : State} {p : Addr} {u : Nat} (hu : u<8)
    (h : InverseTable.Words s.mem p)
    (hr : ∀ off, off+16≤3904 → InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 off) 16)
    (hx : s.gpr .x1=p+BitVec.ofNat 64 (480*u))
    (hq : ∀ e<4, vword (s.v .v31) e=8380417#32) : PackedRoots s (packedRoot u) := by
  refine ⟨hq,fun g _ len _ e _ => packedRoot_range u g len e,?_,?_,?_⟩
  · intro g hg len hl b hb
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    have ho : packedOffset g len≤224 := by
      rcases hl with rfl | rfl <;> simp [packedOffset] <;> omega_using [hg]
    exact hr _ (by rcases hb with rfl | rfl <;> omega_using [hu, ho])
  · intro g hg len hl e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact (packed_words h hu hg hl he).1
  · intro g hg len hl e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    simpa only [Nat.add_assoc] using (packed_words h hu hg hl he).2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

end

@[expose] public section

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
    firstLoads ++ fiveCode ++ firstStores ++ firstAdvance := by kernel_rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
