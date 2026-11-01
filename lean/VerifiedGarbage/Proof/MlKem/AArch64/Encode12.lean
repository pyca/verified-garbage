module

import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Encode
public import VerifiedGarbage.Impl.MlKem.AArch64.Encode
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncBase
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # Public ByteEncode12 proof using eight-coefficient blocks -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Encode12
open VG VG.AArch64
open VG.Impl.MlKem.AArch64 (encode12)

theorem correct (s : State) (hs : encode12AArch64.pre s) :
    ∃ t s', Exec isa encode12 s t s' ∧ abiPreserved s s' ∧ encode12AArch64.post s s' :=
  Codec16.enc_correct s hs

theorem encode12_verified : Verified AArch64.target encode12 (Proof.MlKem.encode12Contract AArch64.abi) :=
  Codec16.enc_verified

end VG.Proof.MlKem.AArch64.Encode12
