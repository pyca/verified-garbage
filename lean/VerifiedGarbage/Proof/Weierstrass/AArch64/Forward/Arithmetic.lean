module

public import VerifiedGarbage.Impl.P256.VerifyArithmetic
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.OptimizeOk
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.P256.VerifyArithmetic

def original (k : Kind) := fprog VG.Impl.P256.VerifyDouble.M (operations k)
def optimized (k : Kind) := VG.Impl.Weierstrass.AArch64.Forward.optimize (original k)

structure Case (k : Kind) where
  checked : OptChecked 8192 (original k) (optimized k)
  leftBound : ∀ i∈original k,instrBound i≤8192
  rightBound : ∀ i∈optimized k,instrBound i≤8192
  clob : ∀ r∈(optimized k).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob 4

abbrev Cases := ∀ k, Case k

theorem refinement (certs : Cases) {M : Mod} {ops : List FOp}
    (sel : selected M ops)
    {base : Addr} {size : Nat} {s : State} (hs : Scr s base size) (hsize : 8192≤size)
    {Q : State → Prop} (hq : WP isa (fprogB M ops) s Q) :
    WP isa (program M ops) s fun t =>
      ∃ u,Q u ∧ t.mem=u.mem ∧ KeepRegs (VG.Proof.Mont.AArch64.clob M.n) s t := by
  rw [program,ite_eq_left sel]
  obtain ⟨rfl,hm⟩ := sel
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hm
  have c := certs k
  have h := c.checked.refine (by decide) (by decide) hs
    (fun i hi => Nat.le_trans (c.leftBound i hi) hsize)
    (fun i hi => Nat.le_trans (c.rightBound i hi) hsize) ((fprogB_wp _ _ (callOf_small (by decide))).mp hq)
  exact WP.mono h fun t ⟨u,hu,he,hk⟩ => ⟨u,hu,he,hk.mono c.clob⟩

/-- Lift a field contract, including algebraic facts independent of machine state. -/
theorem contract (certs : Cases) {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} {V W : List Nat} {E : Nat → Fin m} {s : State} {ops : List FOp}
    {A : Prop} (hs : Scr s base size) (hsize : 8192≤size)
    (hb : WP isa (fprogB M ops) s fun t =>
      ProgKeep M base W s t ∧ Inv M base size m Sl V E t ∧ A) :
    WP isa (program M ops) s fun t =>
      ProgKeep M base W s t ∧ Inv M base size m Sl V E t ∧ A := by
  by_cases sel : selected M ops
  · exact WP.mono (refinement certs sel hs hsize hb)
      fun _ ⟨_,⟨hk,hi,ha⟩,he,kt⟩ => ⟨(transfer_post he kt hk hi).1,(transfer_post he kt hk hi).2,ha⟩
  · rw [program,ite_eq_right sel]
    exact hb

end VG.Proof.Weierstrass.AArch64.Forward.Arithmetic
