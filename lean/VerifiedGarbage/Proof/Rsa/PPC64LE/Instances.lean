module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.InvLaw
import VerifiedGarbage.Proof.Rsa.PPC64LE.IbInverse

/-! # The proofs supplied at the RSA registration on PPC64LE

The batched inverse's contract (`InvLaw`), proved in `IbInverse.lean`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE

instance invLaw : InvLaw where
  inverse_ok := InvBatch.inverse_ok

end VG.Proof.Rsa.PPC64LE
