module

import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
meta import VerifiedGarbage.Impl.MlKem1024.X86_64.Kem
meta import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_check_ek`

The key check of any parameter set (`Proof/MlKem/X86_64/CheckEk.lean`) for
ML-KEM-1024: the 512 groups of `ek[0 : 1536]`.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem.X86_64
open VG.Spec.MlKem

/-- A state satisfying the precondition. -/
def checkEk1024Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1568⟩]
  wr := []

theorem checkEk1024_verified :
    Verified X86_64.target checkEk1024 (Spec.MlKem1024.checkEkContract X86_64.abi) :=
  Verified.of_correct (fun s hs => CheckEk.correct (p := mlKem1024) (by decide) hs)
    (checkEk_ct mlKem1024 (by taint_decide)) (by
    mlkem_implies [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, checkEkC, X86_64.abi,
      X86_64.argRegs, Params.ekLen, mlKem1024] [checkEk1024Sat] using checkEk1024Sat)

end VG.Proof.MlKem1024.X86_64
