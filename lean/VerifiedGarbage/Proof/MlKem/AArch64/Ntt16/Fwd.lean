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
(`NttR.ntt_run`), its constant time (`ct`) and its contract (`ntt_verified`).
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

theorem ct : ConstantTime isa (inPlaceAArch64 Spec.MlKem.ntt).pre (inPlaceAArch64 Spec.MlKem.ntt).pub
    Impl.MlKem.AArch64.Ntt16.ntt :=
  VG.Taint.constantTime (A := VG.AArch64.taint) (VG.AArch64.Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified AArch64.target Impl.MlKem.AArch64.Ntt16.ntt (Proof.MlKem.nttContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Proof.MlKem.nttContract, Proof.MlKem.inPlaceContract, Proof.MlKem.inPlaceSig,
      inPlaceAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Ntt16
