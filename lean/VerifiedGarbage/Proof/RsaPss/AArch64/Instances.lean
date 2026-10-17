module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Tier
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignVerified
public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyVerified
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# RSASSA-PSS on AArch64, for each tier and RSA implementation

The proofs of signing and of verification with cached public-key values,
made with a tier `t` of hash functions (`tierHs t`, the hash function each
number names, `hashAt`) and an implementation `c` of the RSA operation,
which `Generic/MdHashTier/RsaPrivateCrt/AArch64/RsaPss.lean` and
`Generic/MdHashTier/RsaPublicPrecomputed/AArch64/RsaPss.lean` register; and
the CPU features of an instance (`Inst.features`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG.Proof.Pbkdf2.Md.AArch64 (Tier)
open VG.Proof.RsaPkcs1Sig.AArch64 (privOf pdOf)

/-- The hash functions of the tier `t`, by their numbers. -/
def tierHs (t : Tier) : List Impl.Pbkdf2.Md.AArch64.Hash := t.hashes.map (·.H)

theorem tier_length (t : Tier) : t.hashes.length = 8 := by
  simpa using congrArg List.length t.mgf_ok

theorem tier_lt (t : Tier) {k : Nat} (hk : k < 8) : k < t.hashes.length := by rw [tier_length]; exact hk

/-- What the proofs need of the hash function numbered `k` in the tier `t`. -/
def hashAt (t : Tier) (k : Nat) (hk : k < 8) : HashAt (tierHs t) k where
  H := (t.hashes[k]'(tier_lt t hk)).H
  get := by rw [tierHs, List.getElem?_map, List.getElem?_eq_getElem (tier_lt t hk), Option.map_some]
  ok := (t.hashes[k]'(tier_lt t hk)).ok
  Hs := (t.hashes[k]'(tier_lt t hk)).mgf.G
  id := by
    have h := congrArg (·[k]?) t.mgf_ok
    simp only [List.getElem?_map, List.getElem?_eq_getElem (tier_lt t hk), List.getElem?_range hk,
      Option.map_some, Option.some.injEq] at h
    exact h.symm
  hh := (t.hashes[k]'(tier_lt t hk)).mgf.hash
  hl := (t.hashes[k]'(tier_lt t hk)).mgf.len
  hv := Vfy.mgf_valid _
  pss := (t.hashes[k]'(tier_lt t hk)).pss

theorem tierHs_length (t : Tier) : (tierHs t).length ≤ 4096 := by
  rw [tierHs, List.length_map, tier_length]; decide

theorem sign_verified (t : Tier) (c : Proof.Rsa.AArch64.CrtImpl) :
    Verified AArch64.target (Impl.RsaPss.AArch64.sign (tierHs t) (privOf c).name (privOf c).code)
      (Spec.RsaPss.signAnyContract AArch64.abi (Sgn.stk (privOf c).stack)) :=
  Sgn.code_verified (hashAt t) (tierHs_length t) (privOf c)
    (show 16 ≤ Proof.Rsa.AArch64.stackBytes by decide) Sgn.sign_sat

theorem verify_verified (t : Tier) (c : Proof.Rsa.AArch64.PublicImpl) :
    Verified AArch64.target (Impl.RsaPss.AArch64.verifyPrecomputed (tierHs t) (pdOf c).name (pdOf c).code)
      (Spec.RsaPss.verifyAnyContract AArch64.abi (Sgn.stk 16)) :=
  Vfy.code_verified (hashAt t) (tierHs_length t) (pdOf c) (by decide) (Nat.le_refl _) Vfy.verify_sat

namespace Inst

/-- The CPU features of the tier `t` and of an RSA operation's, each once. -/
def features (t : Tier) (cf : List String) : List String := t.features ++ cf.filter (!t.features.contains ·)

end Inst

end VG.Proof.RsaPss.AArch64
