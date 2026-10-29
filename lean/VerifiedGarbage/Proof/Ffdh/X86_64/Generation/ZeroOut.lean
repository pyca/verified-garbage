module
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore

import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # Output clearing from the generation controller's sixteen-word header -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa.X86_64
open VG.WriteBytes (writeW8_apply)

/-- `zeroOut sPtr sLen`: `len` zeros at `op`. -/
theorem controller_zero_out {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 128 ≤ Z)
    {sPtr sLen len : Nat} {op : Addr} (hP : sPtr < 16) (hL : sLen < 16)
    (hO : word s.mem B (8 * sPtr) = op) (hK : word s.mem B (8 * sLen) = BitVec.ofNat 64 len)
    (hk1 : 1 ≤ len) (hk' : len < 2 ^ 31) (o : OutOk s B Z op len) :
    WP isa (zeroOut sPtr sLen) s fun t =>
      (∀ i < len, t.mem (op + BitVec.ofNat 64 i) = 0) ∧
      (∀ x, (∀ j < len, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ Keep [.rsi, .rcx, .rax] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 16, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, hl sPtr hP, hl sLen hL, hO, hK]) rfl) fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_upto (a := 0) (N := len) (by omega) (FailInv s₁ op len) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega), fun x _ => rfl⟩) fun t hI => ?_
  · intro j _ hj t hI
    have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
      rw [hI.keep.2.2, k₁.2.2]; exact o.wr j hj
    have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
        t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
        t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (len - (j + 1)) ∧
        t'.zf = some (decide (j + 1 = len))) (by
      xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
        ofNat64_pred (show 1 ≤ len - j by omega) (by omega), BitVec.add_assoc, ofNat_add_one,
        ofNat64_beq_zero (show len - j - 1 < 2 ^ 64 by omega)]
      exact ⟨by rw [show len - j - 1 = len - (j + 1) by omega], decide_eq_decide.mpr (by omega)⟩) rfl)
      fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
    · intro i hi
      rw [hm, writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) hij))]
        exact hI.bytes i (by omega)
    · intro x hx
      rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
      exact hI.frame x fun i hi => hx i (by omega)
  exact ⟨hI.bytes, fun x hx => by rw [hI.frame x hx, hm₁], (k₁.trans hI.keep).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Generation
