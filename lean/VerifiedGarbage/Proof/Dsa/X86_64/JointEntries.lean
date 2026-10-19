module

import VerifiedGarbage.Proof.Dsa.X86_64.JointStore
public import VerifiedGarbage.Proof.Dsa.X86_64.JointAdvance
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
import Mathlib.Tactic.Set

/-! # Construction of all sixteen joint exponentiation table entries -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure JointBuildInv (t₀ : State) (P : Addr) (w n g y : Nat) (minv : BitVec 64)
    (j : Nat) (t : State) : Prop where
  ctx : JointCtx t P w n minv
  vals : JointBuildValues t.mem P w n g y j
  tab : word t.mem P (8 * Crt.sTab) = off P (slot w 8)
  ent : word t.mem P (8 * Crt.sEnt) = off P (slot w (8 + j))
  entries : ∀ k < j, wv t.mem P (slot w (8 + k)) w =
    (g ^ (k / 4) * y ^ (k % 4)) * 2 ^ (64 * w) % n
  frm : Frm P (workRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

theorem jointBuildStep_ok (M : Mont) {t₀ t : State} {P : Addr} {w n g y j : Nat} {minv : BitVec 64}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hn : 0 < n) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hj : j < 16) (h : JointBuildInv t₀ P w n g y minv j t) :
    WP isa (Joint.buildStep M.mm j) t (JointBuildInv t₀ P w n g y minv (j + 1)) := by
  unfold Joint.buildStep
  refine WP.seq (WP.mono (jointStore_ok h.ctx hw hw' hj h.ent)
    fun v ⟨hc, ha, hh, he, hv, ht, hf, hk⟩ => ?_)
  have vals := h.vals.congr ha
  have entries : ∀ k < j + 1, wv v.mem P (slot w (8 + k)) w =
      (g ^ (k / 4) * y ^ (k % 4)) * 2 ^ (64 * w) % n := by
    intro k hk'
    by_cases he : k = j
    · subst k; exact hv.trans h.vals.entry
    · exact (ht k (by omega) he).trans (h.entries k (by omega))
  refine WP.mono (jointAdvance_ok M hc hw hw' hn hR vals) fun u ⟨hu, hvu, hfu, hku⟩ => ?_
  refine ⟨hu, hvu, (hfu.hslot (by decide)).trans ((hh _ (by decide) (by decide)).trans h.tab),
    (hfu.hslot (by decide)).trans he, ?_, (h.frm.trans hf).trans (arrays_work hfu (by decide)),
    ((h.keep.trans hk).trans hku).mono (by decide)⟩
  intro k hk'
  exact (joint_arrays_entry hfu (by decide) hc.scrT.nowrap (by omega)).trans (entries k hk')

theorem jointBuildSteps_ok (M : Mont) {t₀ t : State} {P : Addr} {w n g y j count : Nat} {minv : BitVec 64}
    (hw : 2 ≤ w) (hw' : w < 2 ^ 30) (hn : 0 < n) (hR : Nat.Coprime (2 ^ (64 * w)) n)
    (hj : j + count ≤ 16) (h : JointBuildInv t₀ P w n g y minv j t) :
    WP isa (Joint.buildSteps M.mm j count) t (JointBuildInv t₀ P w n g y minv (j + count)) := by
  induction count generalizing j t with
  | zero => exact WP.block_nil h
  | succ count ih =>
    unfold Joint.buildSteps
    refine WP.seq (WP.mono (jointBuildStep_ok M hw hw' hn hR (by omega) h) fun u hu => ?_)
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using ih (j := j + 1) (by omega) hu

end VG.Proof.Dsa.X86_64
