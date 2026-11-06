module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Inv
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon

/-!
# ML-KEM's 16-bit inverse NTT on AArch64: `vg_mlkem_ntt_inv`

The inverse NTT (`correctInv`), by the machine of `Proof/MlKem/AArch64/NttR/`
(`NttR.nttInv_run`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

theorem correctInv (s₀ : State) (hs : (inPlaceAArch64 Spec.MlKem.nttInv).pre s₀) :
    ∃ t s', Exec isa Impl.MlKem.AArch64.Ntt16.nttInv s₀ t s' ∧ abiPreserved s₀ s' ∧
      (inPlaceAArch64 Spec.MlKem.nttInv).post s₀ s' := by
  have hp := Ntt.pre_of hs
  suffices h : WP isa Impl.MlKem.AArch64.Ntt16.nttInv s₀ fun s' => s'.sp = s₀.sp ∧
      (inPlaceAArch64 Spec.MlKem.nttInv).post s₀ s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by lit_decide) he (by lit_decide), hpost⟩
  exact NttR.nttInv_run s₀ ⟨hp.wr, hp.disj, hp.red⟩

end VG.Proof.MlKem.AArch64.Ntt16
