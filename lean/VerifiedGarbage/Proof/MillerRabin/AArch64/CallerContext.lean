module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerSave
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrSq
import VerifiedGarbage.Proof.Framework.Omega

/-! # Prepared arithmetic survives saving the round's caller -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.MlKem.AArch64 (Keep)

theorem save_context {s t : State} {B : Addr} {Z w c bm : Nat}
    (hc : MrCtx s B Z w c bm) (he : ECtx s.mem B w c)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hm : t.mem = savedMem s B w) (hk : Keep [.x1, .x2, .x3, .x4, .x19] s t) :
    MrCtx t B Z w c bm ∧ ECtx t.mem B w c := by
  have hpad : pad w + 16 ≤ Z := by
    have hs : slot w 16 ≤ Z := hc.ws.hZ
    simp only [pad, slot, hdrBytes, aOne] at hs ⊢
    omega_arith
  have hout := saved_outside s B w (by have := hc.ws.scr.nowrap; omega_arith)
  have hf : Frm B [(pad w, 16)] s.mem t.mem := by
    rw [hm]
    intro x hx
    exact hout x (hx (pad w, 16) (by simp))
  constructor
  · refine hc.of_frm hf (fun r hr => ?_) hk (by decide) ?_ ?_ ?_ ?_ ?_
    · simp only [List.mem_singleton] at hr
      subst r
      apply Or.inl
      simp only [pad, slot, hdrBytes, aOne]
      omega_arith
    all_goals
      simp only [List.mem_singleton]
      rintro r rfl
      simp only [pad, slot, hdrBytes, aOne, aN, aB, aR1, aRm1, sMinv]
      omega_arith
  · apply he.of_frm hf ?_ (by have := hc.ws.scr.nowrap; omega_arith)
    simp only [List.mem_singleton]
    rintro r rfl
    right
    simp only [pad, slot, hdrBytes, aOne, aE]
    omega_arith

end VG.Proof.MillerRabin.AArch64.Caller
