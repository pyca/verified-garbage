module

public import VerifiedGarbage.Spec.HashTable
public import VerifiedGarbage.Spec.Hmac

/-!
# Tables of HMAC over a hash function: the interface `Hmac`

**Trusted** (as every file in `Spec/`). A function that computes HMAC
(`Spec/Hmac.lean`) over a hash function given at run time takes it as a
table of the interface `Hmac` (`FnTable`, `Abi.withTables`): a read-only
array of `wordCount` pointer-sized words (`param`, a
`*const [usize; wordCount]`), the `as_ptr()` of one of the statics of the
type `Hmac` that the generated crate declares (`fn_tables`), holding the
addresses of `fns` functions, which the function calls indirectly
(`Code.icall`):

0. HMAC's `init`, which keys a streaming state (`vg_hmac_<h>_init`);
1. the hash function's streaming `update`, which HMAC's message goes
   through (HMAC's state is the inner hash's);
2. HMAC's `finalize`, which writes the MAC (`vg_hmac_<h>_finalize`);

then three words of data: the two a table of `Hash` (`Spec/HashTable.lean`)
has, the index of the hash function `H` in `Mgf1.hashes` and its digest
length `hLen` in octets, and HMAC's block size, in octets, which the caller
needs for the counts the streaming `update` and HMAC's `finalize` take (the
inner hash's input starts with a block of key). The table names `H`
(`hashAt`) and HMAC over it with `H`'s block size (`hmacOf H`).

A contract says what a function computes with the HMAC its table names. It
does not say what the table's functions do: the proof of each function
taking one runs the code of the functions of every table of the interface
(each table its registration lists, `Artifact.tables`, which the emitter
checks is every table of `Hmac`), so that it holds only if each table's
functions compute HMAC over the hash function its data names. Which table
is passed is public (`Abi.withTables`): the Rust caller chooses it by the
hash function and the CPU's features.
-/

@[expose] public section

namespace VG.Spec.HmacTable

open Mgf1 (Hash)

/-- The interface's name: the Rust type of its tables. -/
def iface : String := "Hmac"

/-- The number of functions of a table. -/
def fns : Nat := 3

/-- The number of words of a table: its functions', then three of data. -/
def wordCount : Nat := fns + 3

/-- A parameter taking a table of `Hmac`: a `*const [usize; wordCount]`. -/
def param : Param := .table wordCount

/-- The hash function that the table at `p` in the memory `m` names, on a
target with `ptrBits`-bit pointers: that of `Mgf1.hashes` at the index in
its first word of data (its word `fns`, `ptrBits` bits wide, as
`Abi.tableHeld` lays the words out), if there is one. -/
def hashAt (ptrBits : Nat) (m : Mem) (p : Addr) : Option Hash :=
  Mgf1.hashes[(m.readW (p + BitVec.ofNat 64 (ptrBits / 8 * fns)) ptrBits).toNat]?

/-- The hash function `H` for HMAC (`Spec/Hmac.lean`): its digest and its
block size, if this file gives one (the hash functions of FIPS 180-4 and
MD5); by `H`'s Rust name, which is distinct for each. -/
def hmacOf (H : Hash) : Option Hmac.HashFunction :=
  match H.rust with
  | "md5" => some Hmac.md5
  | "sha1" => some Hmac.sha1
  | "sha224" => some Hmac.sha224
  | "sha256" => some Hmac.sha256
  | "sha384" => some Hmac.sha384
  | "sha512" => some Hmac.sha512
  | "sha512_224" => some Hmac.sha512_224
  | "sha512_256" => some Hmac.sha512_256
  | _ => none

/-- Each hash function `hmacOf` gives a block size has the same digest as
its HMAC's. -/
theorem hmacOf_hash : ∀ H ∈ Mgf1.hashes, ∀ F, hmacOf H = some F → F.hash = H.hash := by
  intro H hH F hF
  simp only [Mgf1.hashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [hmacOf, Mgf1.md5, Mgf1.sha1, Mgf1.sha224, Mgf1.sha256, Mgf1.sha384, Mgf1.sha512,
      Mgf1.sha512_224, Mgf1.sha512_256, Mgf1.sha3_224, Mgf1.sha3_256, Mgf1.sha3_384,
      Mgf1.sha3_512, Mgf1.blake2b512, Mgf1.blake2s256, Hmac.md5, Hmac.sha1, Hmac.sha224,
      Hmac.sha256, Hmac.sha384, Hmac.sha512, Hmac.sha512_224, Hmac.sha512_256] <;>
    exact hF ▸ rfl

/-- HMAC's block size over `G`, in octets: that of `hmacOf G`, or 0 if it
gives none. -/
def blockSize (G : Hash) : Nat := ((hmacOf G).map (·.blockSize)).getD 0

/-- The data of a table of HMAC over `G`: its index in `Mgf1.hashes` and its
digest length, as a table of `Hash` of `G` holds, then HMAC's block size. -/
def dataOf (G : Hash) : List (BitVec 64) := HashTable.dataOf G ++ [BitVec.ofNat 64 (blockSize G)]

end VG.Spec.HmacTable
