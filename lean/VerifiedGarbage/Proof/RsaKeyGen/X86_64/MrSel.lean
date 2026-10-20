module
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.RsaKeyGen.Gcd

/-!
# A candidate on x86-64: Miller–Rabin's comparisons

`sel_word`: a word selected by a mask; `eqMask_ok`: the mask of
`[aY] = [j]`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem sel_word (a b : BitVec 64) (c : Bool) : ((a ^^^ b) &&& mask c) ^^^ b = if c then a else b := by
  cases c
  · simp [mask_false]
  · rw [mask_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]; rfl

/-- `eqMask j`: the mask of `[aY] = [j]` into `rbp`, for an extra array `j`. -/
theorem eqMask_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {j : Nat} (hj : 7 < j)
    (hjZ : slot w j + 8 * (w + 2) ≤ Z) :
    WP isa (seqs (eqMask j)) s fun t =>
      t.gpr .rbp = mask (decide (wv s.mem B (slot w aY) w = wv s.mem B (slot w j) w)) ∧ t.mem = s.mem ∧
      Keep [.rax, .rbx, .rbp, .r10, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sY := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  unfold eqMask
  simp only [seqs]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w aY) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aY) (by decide), hg.hdr.hw,
      hg.hdr.harr aY (by decide)]) rfl) fun s₁ ⟨⟨h12, hbx, hm₁⟩, k₁⟩ => ?_
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.mono (extBase_ok hg₁ hZ hw' (j := j) (by omega) (r := .r10) (by decide) rfl rfl)
    fun s₂ ⟨h10, hm₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = 0 ∧ t.mem = s₂.mem) (by xrun) rfl)
    fun s₃ ⟨⟨hbp, hm₃⟩, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  have hs₃ := (hg₁.scr.congr k₂.2.2).congr k₃.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₃.mem → Keep [.r14] s₃ t → t.cf = s₃.cf →
      OrInv s₃ B Z (fun j' => ∀ i < j', word s₃.mem B (slot w aY + 8 * i) = word s₃.mem B (slot w j + 8 * i))
        0 t := fun t h14 hm k _ =>
    ⟨hs₃.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₃.gpr .rbp), hbp]
      exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' _ h0
    (fun i _ hi t hI => xorStep_ok ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hbx))
      ((k₃.gpr (by decide)).trans h10) ((k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)) (by omega)
      (by omega) (by omega) hi hI)) fun s₄ hI => ?_)
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask (decide (s₄.gpr .rbp = 0)) ∧ t.mem = s₄.mem) (by
    xrun
    rw [decide_lt_one]; rfl) rfl) fun t ⟨⟨hbp', hm⟩, k⟩ => ⟨?_, by rw [hm, hI.mem, hm₃, hm₂, hm₁],
      ((k13.trans hI.keep).trans k).mono (by decide)⟩
  rw [hbp']
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hI.val, hm₃, hm₂, hm₁]
  exact ⟨fun h => (wv_congr2 fun i hi => (h i hi).symm).symm, fun h => wv_inj w h⟩

end VG.Proof.RsaKeyGen.X86_64
