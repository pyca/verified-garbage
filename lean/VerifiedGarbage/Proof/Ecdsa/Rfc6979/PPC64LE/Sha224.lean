module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Kit
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Update

/-! # Deterministic ECDSA on PPC64LE: HMAC-SHA-224's functions -/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE

/-- HMAC-SHA-224's functions. -/
def sha224K : Kit :=
  Kit.ofStream Proof.Hmac.Stream.PPC64LE.Sha224.hash Proof.Hmac.Stream.PPC64LE.Sha224.ok Spec.Hmac.sha224I rfl
    Proof.Hmac.Stream.PPC64LE.Sha224.initScratch Proof.Hmac.Stream.PPC64LE.Sha224.finalizeScratch
    Proof.Sha256.PPC64LE.Stream.Update.update_verified.2.1 (by decide) (by decide) (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
