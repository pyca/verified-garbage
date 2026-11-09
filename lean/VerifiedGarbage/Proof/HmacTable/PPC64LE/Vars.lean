module

public import VerifiedGarbage.Proof.HmacTable.PPC64LE
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Hashes

/-!
# Tables of the interface `Hmac` on PPC64LE: the hash functions

The hash functions with HMAC on PPC64LE, MD5, SHA-1 and the SHA-2 family,
one implementation of each (`vars`), for the registrations: their streaming
functions (`Proof/RsaOaep/PPC64LE/Hashes.lean`) and HMAC's `init` and
`finalize` (`Proof/Hmac/Stream/PPC64LE/`). Only the registrations import
them, so that the proofs over any of them do not depend on each one's.
-/

@[expose] public section

namespace VG.Proof.HmacTable.PPC64LE

open VG VG.PPC64LE
open VG.Proof.RsaOaep.PPC64LE

open Proof.Hmac.Stream.PPC64LE in
def md5V : HVar :=
  ⟨_, md5L.ok, md5L.ct, md5L.G, md5L.hash, md5L.len, rfl, Spec.Hmac.md5I, rfl,
    Md5.initScratch, Md5.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha1V : HVar :=
  ⟨_, sha1L.ok, sha1L.ct, sha1L.G, sha1L.hash, sha1L.len, rfl, Spec.Hmac.sha1I, rfl,
    Sha1.initScratch, Sha1.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha224V : HVar :=
  ⟨_, sha224L.ok, sha224L.ct, sha224L.G, sha224L.hash, sha224L.len, rfl, Spec.Hmac.sha224I, rfl,
    Sha224.initScratch, Sha224.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha256V : HVar :=
  ⟨_, sha256L.ok, sha256L.ct, sha256L.G, sha256L.hash, sha256L.len, rfl, Spec.Hmac.sha256I, rfl,
    Sha256.initScratch, Sha256.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha384V : HVar :=
  ⟨_, sha384L.ok, sha384L.ct, sha384L.G, sha384L.hash, sha384L.len, rfl, Spec.Hmac.sha384I, rfl,
    Sha384.initScratch, Sha384.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha512V : HVar :=
  ⟨_, sha512L.ok, sha512L.ct, sha512L.G, sha512L.hash, sha512L.len, rfl, Spec.Hmac.sha512I, rfl,
    Sha512.initScratch, Sha512.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha512_224V : HVar :=
  ⟨_, sha512_224L.ok, sha512_224L.ct, sha512_224L.G, sha512_224L.hash, sha512_224L.len, rfl, Spec.Hmac.sha512_224I,
    rfl, Sha512_224.initScratch, Sha512_224.finalizeScratch⟩
open Proof.Hmac.Stream.PPC64LE in
def sha512_256V : HVar :=
  ⟨_, sha512_256L.ok, sha512_256L.ct, sha512_256L.G, sha512_256L.hash, sha512_256L.len, rfl, Spec.Hmac.sha512_256I,
    rfl, Sha512_256.initScratch, Sha512_256.finalizeScratch⟩

/-- Every hash function with HMAC on PPC64LE. -/
def vars : List HVar := [md5V, sha1V, sha224V, sha256V, sha384V, sha512V, sha512_224V, sha512_256V]

end VG.Proof.HmacTable.PPC64LE
