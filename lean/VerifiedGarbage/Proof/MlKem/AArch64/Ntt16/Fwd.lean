module

import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdU
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.AArch64.Common
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM's 16-bit NTT on AArch64: `vg_mlkem_ntt`

The NTT (`correct`), by the machine of `Proof/MlKem/AArch64/NttR/`
(`NttR.ntt_run`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## The NTT -/

theorem correct (s₀ : State) (hs : (inPlaceAArch64 Spec.MlKem.ntt).pre s₀) :
    ∃ t s', Exec isa Impl.MlKem.AArch64.Ntt16.ntt s₀ t s' ∧ abiPreserved s₀ s' ∧
      (inPlaceAArch64 Spec.MlKem.ntt).post s₀ s' := by
  have hp := Ntt.pre_of hs
  suffices h : WP isa Impl.MlKem.AArch64.Ntt16.ntt s₀ fun s' => s'.sp = s₀.sp ∧
      (inPlaceAArch64 Spec.MlKem.ntt).post s₀ s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by lit_decide) he (by lit_decide), hpost⟩
  exact NttR.ntt_run s₀ ⟨hp.wr, hp.disj, hp.red⟩

end VG.Proof.MlKem.AArch64.Ntt16
