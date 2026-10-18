module

public import VerifiedGarbage.Proof.MlKem.X86_64.DcTop
public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: decapsulation with 16-bit polynomials, K-PKE.Decrypt

`m' = K-PKE.Decrypt(dk_PKE, c)` to `M`, in one call of
`vg_mlkem*_kpke_decrypt` (`dec_ok`, `dec_tr`), and what the rest of
decapsulation with 16-bit polynomials needs of the layout (`Dc16Wf`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps16

open Decaps

variable (K : Kem16)

/-- What `vg_mlkem*_kpke_decrypt` writes. -/
abbrev kdW : List (Ptr × Nat) := [(sc oM, 32), (sc K.oZ, kScr)]

/-- What decapsulation with 16-bit polynomials needs of the layout, evaluated for each parameter set. -/
structure Dc16Wf : Prop extends DcWfB K.L oCT16 where
  kd : kdChk (dcB K.L) (dcW K.L) K.L (sc oM) (.rbp, 0) (.r14, 0) (sc K.oZ) = true
  kdK : dcChk K.L (kdW K) = true

variable {K}

/-- `m'` to `M`. -/
theorem dec_ok (hK : KpkeOk K.L) (W : Dc16Wf K) {σ : State} (hp : (decapsK K.L).pre σ) {s : State} (h : DC K.L σ s)
    (h15 : s.gpr .r15 = 1) : WP isa (K.L.kpkeDecAt (sc oM) (.rbp, 0) (.r14, 0) (sc K.oZ)) s (DM K.L σ) := by
  have L₀ := h.lay W.toDcWfB hp
  refine WP.mono (kpkeDecAt_okL hK L₀ (by decide) (by decide) rbx_na W.kd) fun s' ⟨hP, hm⟩ =>
    ⟨h.step W.toDcWfB hp hP.b W.kdK, by rw [hP.cs .r15 (by decide)]; exact h15, ?_⟩
  rw [hP.pa rbx_cs, hm, h.c, KPke.decM, KPke.dkPke, ← h.dk]
  exact congrArg (kpkeDecrypt K.L.p · _)
    (bytesAt_take _ _ (show 384 * K.L.p.k ≤ 768 * K.L.p.k + 96 by omega)).symm

theorem dec_tr (hK : KpkeOk K.L) (W : Dc16Wf K) :
    RelCT isa (R K.L fun σ s => DC K.L σ s ∧ s.gpr .r15 = 1)
      (K.L.kpkeDecAt (sc oM) (.rbp, 0) (.r14, 0) (sc K.oZ)) fun _ _ => True :=
  rel2_of (kpkeDecAt_trL hK (by decide) (by decide) rbx_na W.kd) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel W.toDcWfB p₁ p₂ pub h₁.1 h₂.1

end Decaps16

end VG.Proof.MlKem.X86_64
