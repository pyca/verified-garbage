module

import VerifiedGarbage.Proof.MlKem.X86_64.CheckEkAvx2
import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk
public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Impl.MlKem1024.X86_64.CheckEkAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.CheckEkAvx2
meta import VerifiedGarbage.Proof.MlKem1024.X86_64.CheckEk
meta import VerifiedGarbage.Spec.MlKem.Contract1024
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.MlKem1024.X86_64.CheckEkAvx2

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_check_ek_avx2`

The key check with AVX2 of any parameter set
(`Proof/MlKem/X86_64/CheckEkAvx2.lean`) for ML-KEM-1024.
-/

@[expose] public section

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem.X86_64
open VG.Spec.MlKem

theorem checkEk1024Avx2_verified :
    Verified X86_64.target checkEk1024Avx2 (Spec.MlKem1024.checkEkContract X86_64.abi) :=
  Verified.of_correct (fun s hs => CkY.correct (p := mlKem1024) (by decide) hs)
    (checkEkAvx2_ct mlKem1024 (by taint_decide)) (by
    mlkem_implies [Spec.MlKem1024.checkEkContract, Spec.MlKem1024.checkEkSig, checkEkC, X86_64.abi,
      X86_64.argRegs, Params.ekLen, mlKem1024] [checkEk1024Sat] using checkEk1024Sat)

end VG.Proof.MlKem1024.X86_64
