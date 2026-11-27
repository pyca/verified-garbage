module

public import VerifiedGarbage.Proof.HmacTable.PPC64LE
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Hashes
import VerifiedGarbage.Proof.Hmac.Generic.Implies

/-!
# Tables of the interface `Hmac` on PPC64LE: the hash functions

The hash functions with HMAC on PPC64LE, MD5, SHA-1 and the SHA-2 family,
one implementation of each (`vars`), for the registrations: their streaming
functions (`Proof/RsaOaep/PPC64LE/Hashes.lean`), HMAC's `init` and
`finalize` (`Proof/Hmac/Stream/PPC64LE/`), and `initLong` with the working
space of HMAC's functions (`<hash>Long`, `longScratchAt`), for a table's
word 0 (`Hash.initAny`). Only the registrations import
them, so that the proofs over any of them do not depend on each one's.
-/

@[expose] public section

namespace VG.Proof.HmacTable.PPC64LE

open VG VG.PPC64LE
open VG.Proof.RsaOaep.PPC64LE
open VG.Proof.Hmac.Stream.PPC64LE.Shared (longScratchContract longPre)

/-- MD5's `initLong` with the working space of HMAC's functions. -/
theorem md5Long : Verified PPC64LE.target Impl.Hmac.Stream.PPC64LE.md5Hash.initLong
    (longScratchContract Spec.Hmac.md5S Spec.Hmac.md5I.scratch) :=
  longScratchAt Proof.Hmac.Stream.PPC64LE.Md5.ok (by decide) Proof.Hmac.Stream.PPC64LE.Md5.long_ct (by
    inst_sat [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5,
      PPC64LE.abi, PPC64LE.argRegs]
      using Proof.Hmac.Stream.PPC64LE.longSat 80 384)

/-- SHA-1's `initLong` with the working space of HMAC's functions. -/
theorem sha1Long : Verified PPC64LE.target Impl.Hmac.Stream.PPC64LE.sha1Hash.initLong
    (longScratchContract Spec.Hmac.sha1S Spec.Hmac.sha1I.scratch) :=
  longScratchAt Proof.Hmac.Stream.PPC64LE.Sha1.ok (by decide) Proof.Hmac.Stream.PPC64LE.Sha1.long_ct (by
    inst_sat [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1,
      PPC64LE.abi, PPC64LE.argRegs]
      using Proof.Hmac.Stream.PPC64LE.longSat 84 448)

/-- SHA-224's `initLong` with the working space of HMAC's functions. -/
theorem sha224Long : Verified PPC64LE.target Impl.Hmac.Stream.PPC64LE.sha224Hash.initLong
    (longScratchContract Spec.Hmac.sha224S Spec.Hmac.sha224I.scratch) :=
  longScratchAt Proof.Hmac.Stream.PPC64LE.Sha224.ok (by decide) Proof.Hmac.Stream.PPC64LE.Sha224.long_ct (by
    inst_sat [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224,
      PPC64LE.abi, PPC64LE.argRegs]
      using Proof.Hmac.Stream.PPC64LE.longSat 96 832)

/-- SHA-256's `initLong` with the working space of HMAC's functions. -/
theorem sha256Long : Verified PPC64LE.target Impl.Hmac.Stream.PPC64LE.sha256Hash.initLong
    (longScratchContract Spec.Hmac.sha256S Spec.Hmac.sha256I.scratch) :=
  longScratchAt Proof.Hmac.Stream.PPC64LE.Sha256.ok (by decide) Proof.Hmac.Stream.PPC64LE.Sha256.long_ct (by
    inst_sat [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256,
      PPC64LE.abi, PPC64LE.argRegs]
      using Proof.Hmac.Stream.PPC64LE.longSat 96 832)

/-- SHA-384's `initLong` with the working space of HMAC's functions. -/
theorem sha384Long : Verified PPC64LE.target Impl.Hmac.Stream.PPC64LE.sha384Hash.initLong
    (longScratchContract Spec.Hmac.sha384S Spec.Hmac.sha384I.scratch) :=
  longScratchAt Proof.Hmac.Stream.PPC64LE.Sha384.ok (by decide) Proof.Hmac.Stream.PPC64LE.Sha384.long_ct (by
    inst_sat [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384,
      PPC64LE.abi, PPC64LE.argRegs]
      using Proof.Hmac.Stream.PPC64LE.longSat 192 1872)

/-- SHA-512's `initLong` with the working space of HMAC's functions. -/
theorem sha512Long : Verified PPC64LE.target Impl.Hmac.Stream.PPC64LE.sha512Hash.initLong
    (longScratchContract Spec.Hmac.sha512S Spec.Hmac.sha512I.scratch) :=
  longScratchAt Proof.Hmac.Stream.PPC64LE.Sha512.ok (by decide) Proof.Hmac.Stream.PPC64LE.Sha512.long_ct (by
    inst_sat [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512,
      PPC64LE.abi, PPC64LE.argRegs]
      using Proof.Hmac.Stream.PPC64LE.longSat 192 1872)

/-- SHA-512/224's `initLong` with the working space of HMAC's functions. -/
theorem sha512_224Long : Verified PPC64LE.target Impl.Hmac.Stream.PPC64LE.sha512_224Hash.initLong
    (longScratchContract Spec.Hmac.sha512_224S Spec.Hmac.sha512_224I.scratch) :=
  longScratchAt Proof.Hmac.Stream.PPC64LE.Sha512_224.ok (by decide) Proof.Hmac.Stream.PPC64LE.Sha512_224.long_ct (by
    inst_sat [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224,
      PPC64LE.abi, PPC64LE.argRegs]
      using Proof.Hmac.Stream.PPC64LE.longSat 192 1872)

/-- SHA-512/256's `initLong` with the working space of HMAC's functions. -/
theorem sha512_256Long : Verified PPC64LE.target Impl.Hmac.Stream.PPC64LE.sha512_256Hash.initLong
    (longScratchContract Spec.Hmac.sha512_256S Spec.Hmac.sha512_256I.scratch) :=
  longScratchAt Proof.Hmac.Stream.PPC64LE.Sha512_256.ok (by decide) Proof.Hmac.Stream.PPC64LE.Sha512_256.long_ct (by
    inst_sat [longScratchContract, longPre, Proof.Hmac.initScratchSig, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256,
      PPC64LE.abi, PPC64LE.argRegs]
      using Proof.Hmac.Stream.PPC64LE.longSat 192 1872)

open Proof.Hmac.Stream.PPC64LE in
def md5V : HVar :=
  ⟨_, md5L.ok, md5L.ct, md5L.G, md5L.hash, md5L.len, rfl, Spec.Hmac.md5I, rfl,
    Md5.initScratch, Md5.finalizeScratch, 6, .inl rfl, rfl,
    md5Long⟩
open Proof.Hmac.Stream.PPC64LE in
def sha1V : HVar :=
  ⟨_, sha1L.ok, sha1L.ct, sha1L.G, sha1L.hash, sha1L.len, rfl, Spec.Hmac.sha1I, rfl,
    Sha1.initScratch, Sha1.finalizeScratch, 6, .inl rfl, rfl,
    sha1Long⟩
open Proof.Hmac.Stream.PPC64LE in
def sha224V : HVar :=
  ⟨_, sha224L.ok, sha224L.ct, sha224L.G, sha224L.hash, sha224L.len, rfl, Spec.Hmac.sha224I, rfl,
    Sha224.initScratch, Sha224.finalizeScratch, 6, .inl rfl, rfl,
    sha224Long⟩
open Proof.Hmac.Stream.PPC64LE in
def sha256V : HVar :=
  ⟨_, sha256L.ok, sha256L.ct, sha256L.G, sha256L.hash, sha256L.len, rfl, Spec.Hmac.sha256I, rfl,
    Sha256.initScratch, Sha256.finalizeScratch, 6, .inl rfl, rfl,
    sha256Long⟩
open Proof.Hmac.Stream.PPC64LE in
def sha384V : HVar :=
  ⟨_, sha384L.ok, sha384L.ct, sha384L.G, sha384L.hash, sha384L.len, rfl, Spec.Hmac.sha384I, rfl,
    Sha384.initScratch, Sha384.finalizeScratch, 7, .inr rfl, rfl,
    sha384Long⟩
open Proof.Hmac.Stream.PPC64LE in
def sha512V : HVar :=
  ⟨_, sha512L.ok, sha512L.ct, sha512L.G, sha512L.hash, sha512L.len, rfl, Spec.Hmac.sha512I, rfl,
    Sha512.initScratch, Sha512.finalizeScratch, 7, .inr rfl, rfl,
    sha512Long⟩
open Proof.Hmac.Stream.PPC64LE in
def sha512_224V : HVar :=
  ⟨_, sha512_224L.ok, sha512_224L.ct, sha512_224L.G, sha512_224L.hash, sha512_224L.len, rfl, Spec.Hmac.sha512_224I,
    rfl, Sha512_224.initScratch, Sha512_224.finalizeScratch, 7, .inr rfl, rfl,
    sha512_224Long⟩
open Proof.Hmac.Stream.PPC64LE in
def sha512_256V : HVar :=
  ⟨_, sha512_256L.ok, sha512_256L.ct, sha512_256L.G, sha512_256L.hash, sha512_256L.len, rfl, Spec.Hmac.sha512_256I,
    rfl, Sha512_256.initScratch, Sha512_256.finalizeScratch, 7, .inr rfl, rfl,
    sha512_256Long⟩

/-- Every hash function with HMAC on PPC64LE. -/
def vars : List HVar := [md5V, sha1V, sha224V, sha256V, sha384V, sha512V, sha512_224V, sha512_256V]

end VG.Proof.HmacTable.PPC64LE
