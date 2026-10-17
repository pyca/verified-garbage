module

public import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hash
public import VerifiedGarbage.Proof.Mgf1.Basic
public import VerifiedGarbage.Spec.HashId

/-!
# RSASSA-PSS on AArch64: the hash functions by their numbers

What the proofs of signing and verification need of the hash function
numbered `k` among a tier's `hs` (`HashAt`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-- What the proofs need of the hash function numbered `k` among `hs`. -/
structure HashAt (hs : List Hash) (k : Nat) where
  H : Hash
  get : hs[k]? = some H
  ok : HashOK H
  Hs : Spec.Mgf1.Hash
  id : Spec.HashId.mgf1 k = some Hs
  hh : ∀ x, Hs.hash x = ok.SH.H.hash x
  hl : Hs.len = H.D
  hv : Proof.Mgf1.Valid Hs
  pss : PssChecks H.P H.D

end VG.Proof.RsaPss.AArch64
