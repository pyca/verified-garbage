module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Normalize
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Normalizing unused bookkeeping preserves the prepared round -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MlKem.X86_64

private theorem below_arrays (w j : Nat) :
    ∀ r ∈ [(128, 128)], slot w j + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  right
  simp only [slot, hdrBytes]
  omega_arith

theorem normalized_ctx {s t : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (h : MrDims B Z w) (he : ECtx s.mem B w c)
    (hm : t.mem = normalizedMem s.mem B w) (hk : Keep [.rax] s t) :
    MrCtx t B Z w mi c bm ∧ ECtx t.mem B w c := by
  have hf : Frm B [(128, 128)] s.mem t.mem := by
    rw [hm]
    exact Frm.of_outside (normalized_outside s.mem B w) (List.mem_singleton_self _)
  refine ⟨hc.of_frm h hf (hc.good.scr.congr hk.2.2) ((hk.gpr (by decide)).trans hc.good.rdi)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact Nat.le_refl 128)
    (below_arrays w aN) (below_arrays w aB) (below_arrays w aR1) (below_arrays w aRm1), ?_⟩
  have hn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64 := by
    have := aE_fits h
    have := hc.good.scr.nowrap
    omega_arith
  exact he.of_frm hf (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    right
    simp only [slot, hdrBytes]
    omega_arith) hn

end VG.Proof.MillerRabin.X86_64
