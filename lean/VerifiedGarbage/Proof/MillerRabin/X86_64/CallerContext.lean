module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerSave
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq
import VerifiedGarbage.Proof.Framework.Omega

/-! # Saving the workspace preserves its mathematical preparation -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Caller

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Impl.MillerRabin.X86_64.Caller
open VG.Proof.MlKem.X86_64

theorem save_context {s t : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c) (hd : MrDims B Z w)
    (hm : t.mem = savedMem s B w) (hk : Keep [.rax, .rbx, .rcx, .rdx, .rsi] s t) :
    MrCtx t B Z w mi c bm ∧ ECtx t.mem B w c := by
  have hn := hc.good.scr.nowrap
  have hpad : pad w + 8 ≤ Z := by
    have hz := hd.x
    simp only [pad, slot, hdrBytes, aR1, aRm1] at hz ⊢
    omega_arith
  have hf : Frm B [(pad w, 8)] s.mem t.mem := by
    rw [hm]
    intro x hx
    exact saved_outside s B w (by omega_arith) x (hx (pad w, 8) (by simp))
  refine ⟨hc.of_frm hd hf (hc.good.scr.congr hk.2.2)
    ((hk.gpr (by decide)).trans hc.good.rdi) ?_ ?_ ?_ ?_ ?_,
    he.of_frm hf ?_ (by have := aE_fits hd; omega_arith)⟩
  all_goals
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
  · simp only [pad, slot, hdrBytes, aR1]; omega_arith
  · left; simp only [pad, slot, hdrBytes, aR1, aN]; omega_arith
  · left; simp only [pad, slot, hdrBytes, aR1, aB]; omega_arith
  · left; simp only [pad]; omega_arith
  · right; simp only [pad, slot, hdrBytes, aR1, aRm1]; omega_arith
  · left; simp only [pad, slot, hdrBytes, aR1, aE]; omega_arith

end VG.Proof.MillerRabin.X86_64.Caller
