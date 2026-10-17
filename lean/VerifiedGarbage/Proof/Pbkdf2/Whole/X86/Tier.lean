module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
public import VerifiedGarbage.Spec.HashId
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Sha1.Md
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Tiers of HMAC's hash functions on x86 (32-bit)

A function that takes the hash function as an argument (by its number,
`Spec/HashId.lean`) calls the one its argument names through a dispatch
(`Impl/Dispatch/X86.lean`), so each of its instances calls one
implementation of each hash function: a `Tier`, a variant of the interface
`HmacTier` on x86 (`Variants/HmacTier/X86/`). Its hash functions are those
of `HashId` from 1 to 7 (SHA-1 to SHA-512/256), in that order (`hmac_ok`),
each as the functions HMAC's callers call (`Impl.Pbkdf2.Whole.X86.Fns`:
HMAC's `init` and `finalize` and the streaming `update`, PBKDF2's), verified
(`FnsOK`), made with one implementation of each compression function:
SHA-1's and SHA-256's (for SHA-224 and SHA-256); SHA-512's has one, the
scalar code (`Tier.of`). An instance needs the CPU features of all of them,
and its name ends with the tier's suffix, qualified by its interface's tag
(`Emit.qualifiedName`), e.g. `vg_ecdsa_p256_rfc6979_sign_hash_shani`.

Each tier is the fastest implementation of each compression function on a
kind of CPU, as `src/hashes/` chooses them: so its suffix names the CPU
features that choose them.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)

/-- The output and block sizes of SHA-1 and the SHA-2 functions. -/
def dbSizes : List (Nat × Nat) := [(20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- A hash function: the functions HMAC's callers call, verified, its
digests' length, and the sizes its callers lay out their memory for: output
and block sizes of SHA-1 or SHA-2, and states and working space no larger
than SHA-512's. -/
structure TierHash where
  F : Fns
  ok : FnsOK F
  macLen : ∀ x, (ok.hH.SH.H.hash x).length = F.H.D
  hDB : (F.H.D, F.H.B) ∈ dbSizes
  hS : F.H.S ≤ 192
  hWi : ok.Wi * 8 ≤ 1872
  hWf : ok.Wf * 8 ≤ 1872

/-- A tier: an implementation of each hash function, by its number. -/
structure Tier where
  /-- What the names of its instances end with (e.g. `_shani`; nothing for
  the baseline implementations). -/
  suffix : String
  /-- SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
  SHA-512/256: the hash function `i` names is the `(i - 1)`th. -/
  hashes : List TierHash
  /-- They are those `HashId.hmac` numbers, as HMAC takes them. -/
  hmac_ok : hashes.map (some ·.ok.hH.SH.H) = [1, 2, 3, 4, 5, 6, 7].map Spec.HashId.hmac
  /-- Their output lengths are those `HashId.mgf1` gives. -/
  len_ok : hashes.map (some ·.F.H.D) = [1, 2, 3, 4, 5, 6, 7].map fun i => (Spec.HashId.mgf1 i).map (·.len)
  /-- The CPU features of their implementations, each once. -/
  features : List String

/-- The hash functions of a tier, with their numbers. -/
def Tier.fns (t : Tier) : List (Nat × Fns) := (List.range t.hashes.length).zipWith (fun i h => (i + 1, h.F)) t.hashes

theorem sha1_len (x : List Byte) : (Spec.Sha1.hash x).length = 20 := by
  rw [Proof.Sha1.hash_eq]; exact Proof.Sha1.md.digest_length _

theorem sha256_len (x : List Byte) : (Spec.Sha256.hash x).length = 32 := by
  rw [Proof.Sha256.hash_eq]; exact Proof.Sha256.md.digest_length _

theorem sha224_len (x : List Byte) : (Spec.Sha256.sha224 x).length = 28 := by
  simp [Spec.Sha256.sha224, Spec.Sha256.finalHash, Spec.Sha256.wordBytes, List.length_flatMap, List.map_const']

theorem sha512_len (x : List Byte) : (Spec.Sha512.finalHash Spec.Sha512.H0_512 x).length = 64 :=
  Proof.Hmac.Generic.Common.finalHash_length _ _

theorem sha512t_len (n : Nat) (h : n ≤ 64) (H0 : Spec.Sha512.HashValue) (x : List Byte) :
    ((Spec.Sha512.finalHash H0 x).take n).length = n := by
  rw [List.length_take, Proof.Hmac.Generic.Common.finalHash_length]; omega

/-- The tier of an implementation of SHA-1's (`v1`) and SHA-256's (`v256`)
compression functions. -/
def Tier.of (suffix : String) (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend) :
    Tier where
  suffix := suffix
  hashes := [
    { F := v1.F, ok := sha1OKF v1, macLen := sha1_len, hDB := show (20, 64) ∈ dbSizes by decide,
      hS := show 84 ≤ 192 by decide, hWi := show 56 * 8 ≤ 1872 by decide, hWf := show 56 * 8 ≤ 1872 by decide },
    { F := v256.F224, ok := sha224OKF v256, macLen := sha224_len, hDB := show (28, 64) ∈ dbSizes by decide,
      hS := show 96 ≤ 192 by decide, hWi := show 104 * 8 ≤ 1872 by decide, hWf := show 104 * 8 ≤ 1872 by decide },
    { F := v256.F, ok := sha256OKF v256, macLen := sha256_len, hDB := show (32, 64) ∈ dbSizes by decide,
      hS := show 96 ≤ 192 by decide, hWi := show 104 * 8 ≤ 1872 by decide, hWf := show 104 * 8 ≤ 1872 by decide },
    { F := sha384F, ok := sha384OKF, macLen := sha512t_len 48 (by decide) _, hDB := by decide, hS := by decide,
      hWi := by decide, hWf := by decide },
    { F := sha512F, ok := sha512OKF, macLen := sha512_len, hDB := by decide, hS := by decide,
      hWi := by decide, hWf := by decide },
    { F := sha512_224F, ok := sha512_224OKF, macLen := sha512t_len 28 (by decide) _, hDB := by decide,
      hS := by decide, hWi := by decide, hWf := by decide },
    { F := sha512_256F, ok := sha512_256OKF, macLen := sha512t_len 32 (by decide) _, hDB := by decide,
      hS := by decide, hWi := by decide, hWf := by decide }]
  hmac_ok := rfl
  len_ok := rfl
  features := (v1.features ++ v256.features).eraseDups

end VG.Proof.Pbkdf2.Whole.X86
