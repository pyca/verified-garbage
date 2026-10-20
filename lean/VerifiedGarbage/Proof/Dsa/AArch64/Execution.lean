module

public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Call
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import VerifiedGarbage.Proof.Dsa.Layout
public import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! # Persistent state across DSA arithmetic and validation schedules -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ExecutionLayout where
  base : Addr
  pLen : Nat
  qLen : Nat
  modulus : Nat
  subgroup : Nat
  pInverse : BitVec 64
  qInverse : BitVec 64
  fields : Field → BitVec 64
  lengths : Spec.Dsa.lengthsValid pLen qLen
  pLength : fields .pLen = BitVec.ofNat 64 pLen
  qLength : fields .qLen = BitVec.ofNat 64 qLen

abbrev ExecutionLayout.pWords (L : ExecutionLayout) : Nat := (L.pLen + 7) / 8
abbrev ExecutionLayout.qWords (L : ExecutionLayout) : Nat := (L.qLen + 7) / 8

structure Ready (L : ExecutionLayout) (s : State) : Prop where
  parent : Good s L.base activeBytes outerWords 0
  scratch : Scr s L.base usedBytes
  fields : ∀ f : Field, f ≠ .mask → word s.mem L.base f.offset = L.fields f
  pChild : ChildReady s.mem L.base pWorkspace L.pWords L.modulus L.pInverse
  qChild : ChildReady s.mem L.base qWorkspace L.qWords L.subgroup L.qInverse

theorem Ready.afterP {L : ExecutionLayout} {s t : State} {d k : Nat}
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hc : ChildReady t.mem L.base pWorkspace L.pWords L.modulus L.pInverse)
    (hf : CallFrame L.base pWorkspace L.pWords (off L.base d) k s.mem t.mem)
    (hk : Keep coreRegs s t) (hd : activeBytes ≤ d) (hend : d + k ≤ usedBytes) : Ready L t := by
  obtain ⟨_, _, _, _, _, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ qWorkspace at hpHi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqHi
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hau : activeBytes ≤ usedBytes := by decide
  have hn := h.scratch.nowrap
  have hlf := callFrame_local hf (by omega) (by omega)
  refine ⟨hp, h.scratch.congr hk.wr, ?_, hc, ?_⟩
  · intro f hm
    exact (localCall_field hlf (Nat.le_refl _) (Nat.le_trans (by decide) hd) f).trans (h.fields f hm)
  · exact localCall_ready hlf h.qChild (by decide) (by omega) (Or.inr hpHi) (Or.inl (by omega))

theorem Ready.afterQ {L : ExecutionLayout} {s t : State} {d k : Nat}
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hc : ChildReady t.mem L.base qWorkspace L.qWords L.subgroup L.qInverse)
    (hf : CallFrame L.base qWorkspace L.qWords (off L.base d) k s.mem t.mem)
    (hk : Keep coreRegs s t) (hd : activeBytes ≤ d) (hend : d + k ≤ usedBytes) : Ready L t := by
  obtain ⟨_, _, _, _, _, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ qWorkspace at hpHi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqHi
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hau : activeBytes ≤ usedBytes := by decide
  have hn := h.scratch.nowrap
  have hlf := callFrame_local hf (by omega) (by omega)
  refine ⟨hp, h.scratch.congr hk.wr, ?_, ?_, hc⟩
  · intro f hm
    exact (localCall_field hlf (by decide) (Nat.le_trans (by decide) hd) f).trans (h.fields f hm)
  · exact localCall_ready hlf h.pChild (by decide) (by omega) (Or.inl (by omega)) (Or.inl (by omega))

theorem Ready.local_write {L : ExecutionLayout} {s : State} {d k : Nat} (h : Ready L s)
    (hend : d + k ≤ usedBytes) : ∀ i < k, InRegions s.wr (off L.base d + BitVec.ofNat 64 i) 1 := by
  intro i hi
  rw [show off L.base d + BitVec.ofNat 64 i = off L.base (d + i) by simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
  exact h.scratch.st1 (by omega)

theorem Ready.local_out {L : ExecutionLayout} {s : State} {d k : Nat} (h : Ready L s)
    (hd : activeBytes ≤ d) (hend : d + k ≤ usedBytes) :
    ∀ i < k, activeBytes ≤ ofs L.base (off L.base d + BitVec.ofNat 64 i) := by
  intro i hi
  rw [ofs_off L.base (by have := h.scratch.nowrap; omega)]
  omega

end VG.Proof.Dsa.AArch64
