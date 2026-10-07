import VerifiedGarbage.Impl.P256.VerifyAllocated
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Observed
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame

namespace VG.Proof.P256.VerifyAllocated
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.Forward
open VG.Impl.P256.VerifyArithmetic

/-- Dead doubling intermediates and private spill words are not observed. -/
def observe (k : Kind) (off : Nat) : Prop :=
  (k≠.doubleRR ∨ off<800 ∨ 992≤off) ∧ (off<7104 ∨ 7680≤off)
instance (k : Kind) (off : Nat) : Decidable (observe k off) := by
  unfold observe; infer_instance

def work : List (Nat × Nat) := [(512,480),(128,32),(7104,576)]

structure Case (k : Kind) where
  checked : CheckedObserved 8192 (observe k)
    (VG.Impl.P256.VerifyAllocated.raw k) (VG.Impl.P256.VerifyAllocated.code k)
  inputs : Inputs checked.nodes 8192
  initial : checked.initial=initialEnv
  leftBound : ∀ i∈VG.Impl.P256.VerifyAllocated.raw k,instrBound i≤8192
  rightBound : ∀ i∈VG.Impl.P256.VerifyAllocated.code k,instrBound i≤8192
  clob : ∀ r∈(VG.Impl.P256.VerifyAllocated.code k).flatMap instrClob,r∈allocatedRegs
  writes : ∀ w∈(VG.Impl.P256.VerifyAllocated.code k).flatMap instrWrites,
    ∃ w'∈work,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2

theorem Case.refine {k : Kind} (c : Case k) {base : Addr} {s : State}
    (hs : Scr s base 8192) {Q : State → Prop}
    (hq : WP isa (.block (VG.Impl.P256.VerifyAllocated.raw k)) s Q) :
    WP isa (VG.Impl.P256.VerifyAllocated.program k) s fun t => ∃ u,Q u ∧
      (∀ off,observe k off → off%8=0 → off+8≤8192 →
        word t.mem base off=word u.mem base off) ∧ AllocatedFrame allocatedRegs base work s t := by
  have he : Rel (nodeVal c.checked.nodes (word s.mem base)) base 8192 c.checked.initial s := by
    rw [c.initial]
    exact initial_rel c.inputs s base
  exact WP.mono (c.checked.refine (word s.mem base) (by decide) hs he c.leftBound c.rightBound hq)
    fun _ ⟨u,hu,hw,hk,hm⟩ => ⟨u,hu,hw,hk.mono c.clob,hm.cover c.writes⟩

end VG.Proof.P256.VerifyAllocated
