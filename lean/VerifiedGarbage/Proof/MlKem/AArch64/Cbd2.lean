module

import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16
public import VerifiedGarbage.Impl.MlKem.AArch64.Encode
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Base
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # Public CBD2 proof, using sixteen byte lanes -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd2
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (cbd2)

theorem correct (s : State) (hs : cbd2AArch64.pre s) :
    ∃ t s', Exec isa cbd2 s t s' ∧ abiPreserved s s' ∧ cbd2AArch64.post s s' :=
  Cbd16.correct s hs

theorem cbd2_verified : Verified AArch64.target cbd2 (Proof.MlKem.cbd2Contract AArch64.abi) :=
  Cbd16.verified

end VG.Proof.MlKem.AArch64.Cbd2
