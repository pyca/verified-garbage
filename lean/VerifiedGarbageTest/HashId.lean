import VerifiedGarbage.Spec.HashId
import VerifiedGarbage.Spec.RsaPkcs1Sig
import VerifiedGarbage.Spec.RsaOaep.AnyHash
import VerifiedGarbage.Spec.RsaPss.AnyHash
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.AnyHash
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P521Sha512
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.TCB.X86_64.Target

/-!
# The numbers of the hash functions

The numbers that the functions taking a hash function as an argument use
(`HashId.mgf1`, `HashId.hmac`) are those of `RsaPkcs1Sig.Hash.ofId` (by name
and digest length) wherever both name a hash function; `HashId.hmac` names
the same hash functions as `HashId.mgf1`; and `RsaOaep.hashIds`,
`RsaPss.hashIds` and `Ecdsa.Rfc6979.hashIds` name the hash functions their
documentation says. Every target's calling convention models their
arguments (otherwise their contracts' precondition would be `False`): on
AArch64, Apple's packs narrow arguments on the stack, which `AArch64.abi`
accepts only as the first one.
-/

namespace VG.Test.HashId

open VG.Spec

/-- The name of the constructor `h`, as `Mgf1.Hash.rust` spells it. -/
def ctorName (h : RsaPkcs1Sig.Hash) : String := ((reprStr h).splitOn ".").getLast!

#guard (List.range 16).all fun i =>
  (HashId.mgf1 i).map (fun H => (H.rust, H.len)) ==
    (RsaPkcs1Sig.Hash.ofId i).map (fun h => (ctorName h, h.len)) ||
  (12 ≤ i && (RsaPkcs1Sig.Hash.ofId i).isNone)

#guard (List.range 16).all fun i => (HashId.hmac i).isSome == decide (i < 8)

example : (HashId.hmac 0).map (·.hash) = (HashId.mgf1 0).map (·.hash) := rfl
example : (HashId.hmac 1).map (·.hash) = (HashId.mgf1 1).map (·.hash) := rfl
example : (HashId.hmac 2).map (·.hash) = (HashId.mgf1 2).map (·.hash) := rfl
example : (HashId.hmac 3).map (·.hash) = (HashId.mgf1 3).map (·.hash) := rfl
example : (HashId.hmac 4).map (·.hash) = (HashId.mgf1 4).map (·.hash) := rfl
example : (HashId.hmac 5).map (·.hash) = (HashId.mgf1 5).map (·.hash) := rfl
example : (HashId.hmac 6).map (·.hash) = (HashId.mgf1 6).map (·.hash) := rfl
example : (HashId.hmac 7).map (·.hash) = (HashId.mgf1 7).map (·.hash) := rfl

/-- The SHA-1 and SHA-2 functions' names. -/
def sha12 : List (Option String) :=
  [some "sha1", some "sha224", some "sha256", some "sha384", some "sha512", some "sha512_224",
    some "sha512_256"]

#guard RsaOaep.hashIds.map (fun i => (HashId.mgf1 i).map (·.rust)) == sha12
#guard Ecdsa.Rfc6979.hashIds.map (fun i => (HashId.mgf1 i).map (·.rust)) == sha12
#guard RsaPss.hashIds.map (fun i => (HashId.mgf1 i).map (·.rust)) == some "md5" :: sha12

/-- Whether `A` models the arguments of `sig`. -/
def modeled {M : ISA} (A : Abi M) (sig : Sig) : Bool :=
  (A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits))).isSome

/-- The signatures taking hash functions as arguments. -/
def sigs : List Sig :=
  [RsaOaep.encryptAnySig, RsaOaep.decryptAnySig, RsaPss.signAnySig, RsaPss.verifyAnySig,
    Ecdsa.Rfc6979.Instance.signAnySig Ecdsa.Rfc6979.P521Sha512.inst]

#guard sigs.all (modeled AArch64.abi)
#guard sigs.all (modeled Arm.abi)
#guard sigs.all (modeled X86.abi)
#guard sigs.all (modeled X86_64.abi)

end VG.Test.HashId
