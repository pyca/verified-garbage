module

import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Decode
public import VerifiedGarbage.Impl.MlKem.AArch64.Encode
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # Public ByteDecode12 proof using eight-coefficient blocks -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Decode12
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (decode12)

theorem correct (s : State) (hs : decode12AArch64.pre s) :
    ∃ t s', Exec isa decode12 s t s' ∧ abiPreserved s s' ∧ decode12AArch64.post s s' :=
  Codec16.dec_correct s hs

theorem decode12_verified : Verified AArch64.target decode12 (Proof.MlKem.decode12Contract AArch64.abi) :=
  Codec16.dec_verified

end VG.Proof.MlKem.AArch64.Decode12
