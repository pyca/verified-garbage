module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512

/-! # Ed25519's whole functions on PPC64LE: SHA-512's streaming functions

What the proofs need of them (`ShaOK`), from HMAC's proofs: the one module of
Ed25519's whole functions that imports SHA-512's proofs, besides the theorems
stating the functions' contracts. -/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

def sha512OK : ShaOK := ⟨Proof.Hmac.Stream.PPC64LE.Sha512.ok, rfl, rfl⟩

end VG.Proof.Ed25519.PPC64LE.Whole
