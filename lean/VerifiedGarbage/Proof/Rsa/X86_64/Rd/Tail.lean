module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Stages
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the square root and the factors

The square root's stage (`sqrtS_ok`): `rootOf`'s root, and the mask and'ed
with whether its remainder is zero; the factors `(b + ϒ) / 2` and
`(b - ϒ) / 2`, written under the mask, and the exit (`factors_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet

/-- What the square root's stage changes: arrays 4 to 7, wide array 7, the
mask and the header slots 25 and 30. -/
def SqP (w y : Nat) : Prop :=
  (slot w 4 ≤ y ∧ y < slot w 8) ∨ (slot w 14 ≤ y ∧ y < slot w 14 + 8 * (2 * w + 2)) ∨ (200 ≤ y ∧ y < 208) ∨
    (240 ≤ y ∧ y < 248) ∨ (176 ≤ y ∧ y < 184)

macro "sqs_omega" : tactic =>
  `(tactic| (simp only [SqP, SqrtP, DOk, Bignum.slot, hdrBytes, Impl.Bignum.X86_64.Public.sMask, sFn, sCt, sC]; omega_arith))

/-- The square root's stage (narrow): `64 (w + 1)` steps of `sqrtStep` from `X`
(wide array 7), the root into array 5, and the mask and'ed with whether
the remainder is zero. -/
theorem sqrtS_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {X : Nat} {c : Bool}
    (hX : wv s.mem B (slot w 14) (2 * w + 2) = X) (hz : wv s.mem B (slot w 3) w = 0) (hm : mw s.mem B = mask c) :
    WP isa (seqs RecoverDet.sqrt) s fun t =>
      wv t.mem B (slot w 5) w = ((sqrtStep (64 * w) (64 * (2 * w + 2)))^[64 * (w + 1)] (X, 0, 0)).2.2 ∧
      mw t.mem B = mask (c && decide (((sqrtStep (64 * w) (64 * (2 * w + 2)))^[64 * (w + 1)] (X, 0, 0)).2.1 = 0)) ∧
      FrmP B (SqP w) s.mem t.mem ∧ Keep [.r12, .r9, .r8, .rax, .r14, .rbx, .rbp, .rsi, .r10, .rdx] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have hw1 := h.w1
  simp only [RecoverDet.sqrt, List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.mono (zeroA_ok h (j := 4) (by decide)) fun t₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (by sqs_omega) k1 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := 5) (by decide)) fun t₂ ⟨z2, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (by sqs_omega) k2 (by simp)
  refine WP.seq (WP.mono (countW_ok h₂) fun t₃ ⟨m3, k3⟩ => ?_)
  have h₃ := h₂.congrW m3 (by sqs_omega) (by decide) k3 (by simp)
  have o3 : Outside B (8 * sCt) 8 t₂.mem t₃.mem := by rw [m3]; exact writeW_outside _ _ _ (by sqs_omega)
  have X₃ : wv t₃.mem B (slot w 14) (2 * w + 2) = X := by
    rw [o3.wv (by sqs_omega) (by sqs_omega), o2.wv (by sqs_omega) (by sqs_omega), o1.wv (by sqs_omega) (by sqs_omega), hX]
  have R₃ : wv t₃.mem B (slot w 4) w = 0 := by
    rw [o3.wv (by sqs_omega) (by sqs_omega), o2.wv (by sqs_omega) (by sqs_omega),
      wv_low_of_lt (v := w) (w := w + 2) (by omega_arith) (by rw [z1]; exact Nat.two_pow_pos _), z1]
  have Y₃ : wv t₃.mem B (slot w 5) w = 0 := by
    rw [o3.wv (by sqs_omega) (by sqs_omega),
      wv_low_of_lt (v := w) (w := w + 2) (by omega_arith) (by rw [z2]; exact Nat.two_pow_pos _), z2]
  have hct : word t₃.mem B (8 * sCt) = BitVec.ofNat 64 (64 * (w + 1)) := by rw [m3, word_writeW_self]
  -- The loop.
  refine wp_seqs_append (a := [.loop sqrtBody .ne]) (by simp) (by simp)
    (WP.mono (sqrtLoop_ok h₃ hct) fun t₄ hI => ?_)
  rw [X₃, R₃, Y₃] at hI
  have h₄ := hI.ws
  have hv := hI.val
  -- Whether the remainder is zero.
  have hz₄ : wv t₄.mem B (slot w 3) w = 0 := by
    rw [hI.frm.wv_eq (fun y => by sqs_omega) (by sqs_omega), o3.wv (by sqs_omega) (by sqs_omega),
      o2.wv (by sqs_omega) (by sqs_omega), o1.wv (by sqs_omega) (by sqs_omega), hz]
  refine wp_seqs_append (by simp [eqA]) (by simp) (WP.mono (eqA_ok h₄ (a := 4) (b := 3) (by decide) (by decide))
    fun t₅ ⟨hz5, m5, k5⟩ => ?_)
  rw [hz₄] at hz5
  have h₅ := h₄.congrP (FrmP.of_eq (P := fun _ => False) m5) (fun y hy => hy.elim) k5 (by simp)
  have hm₅ : mw t₅.mem B = mask c := by
    unfold mw at hm ⊢
    rw [m5, hI.frm.word_eq (fun y => by sqs_omega) (by sqs_omega), o3.word (by sqs_omega) (by sqs_omega),
      o2.word (by sqs_omega) (by sqs_omega), o1.word (by sqs_omega) (by sqs_omega), hm]
  simp only [seqs]
  refine WP.mono (andZero_ok h₅ hm₅ hz5) fun t ⟨m6, k6⟩ => ?_
  have o6 : Outside B (8 * Impl.Bignum.X86_64.Public.sMask) 8 t₅.mem t.mem := by
    rw [m6]; exact writeW_outside _ _ _ (by sqs_omega)
  have fr : ∀ {o n : Nat} {m m' : Mem}, Outside B o n m m' → (∀ y, o ≤ y → y < o + n → SqP w y) →
      FrmP B (SqP w) m m' := fun ho hP => FrmP.of_out ho hP
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [o6.wv (by sqs_omega) (by sqs_omega), m5]
    exact congrArg (fun p => p.2.2) hv
  · unfold mw
    rw [m6, word_writeW_self, ← congrArg (fun p => p.2.1) hv]
  · exact ((((((fr o1 fun y => by sqs_omega).trans (fr o2 fun y => by sqs_omega)).trans
      (fr o3 fun y => by sqs_omega)).trans (hI.frm.mono fun y => by sqs_omega)).trans (FrmP.of_eq m5)).trans
      (fr o6 fun y => by sqs_omega))
  · exact (((((k1.trans k2).trans k3).trans hI.keep).trans k5).trans k6).mono (by simp)

end VG.Proof.Rsa.X86_64.Rd
