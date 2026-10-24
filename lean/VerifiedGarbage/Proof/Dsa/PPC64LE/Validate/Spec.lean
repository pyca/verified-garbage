module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.Validation
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA public-key validation on PPC64LE: the specification

`validate_spec`: the specification's validation of the packed key at `key`
is `KeyOk`, the checks `checkKey` makes.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

instance instDecidableKeyOk (m : Mem) (L : Lay) (key : Addr) : Decidable (KeyOk m L key) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem validate_spec {m : Mem} {L : Lay} {key : Addr} (hv : Spec.Dsa.lengthsValid L.pl L.ql) :
    Spec.Dsa.validatePublicKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m key (3 * L.pl + L.ql)) =
      decide (KeyOk m L key) :=
  VG.Proof.Dsa.validatePublicKeyBytes_eq hv (VG.Proof.Bignum.bytesAt_length _ _ _)
    (VG.Proof.Dsa.publicKeyBytes_at m key (Nat.le_refl _))

end VG.Proof.Dsa.PPC64LE
