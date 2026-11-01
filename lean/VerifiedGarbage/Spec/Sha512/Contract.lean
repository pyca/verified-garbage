module

public import VerifiedGarbage.Spec.Sha512
public import VerifiedGarbage.TCB.Artifact

/-!
# SHA-512: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of streaming SHA-384,
SHA-512, SHA-512/224 and SHA-512/256 (`init`/`update`/`finalize`, on the
representation `Repr`), in terms of `Spec/Sha512.lean`, for any target:
`A` is the target's calling convention.
`finalize` writes the final hash value, from any initial hash value; the
`finalize` of SHA-384, SHA-512/224 and SHA-512/256 (`finalizeDigestApi`)
writes the algorithm's digest, the whole result of FIPS 180-4. `digest`
(`digestApi`) computes a member's digest of a message in memory in one call,
with no streaming state.
The signatures fix where the arguments are, the memory each function may
access, disjointness, and that the pointers and lengths are public (see
`TCB/Sig.lean`); the contracts add the postconditions and which other
arguments are public.

`update`, `finalize` and `digest` take the number of bytes of stack below the stack pointer that
an implementation's calls and frames use (`stack`, see `Sig.contract`), 0 for
one that uses none: it depends on the target, and on which functions the
implementation calls. They keep their working space there.
-/

@[expose] public section

namespace VG.Spec.Sha512

/-- `vg_<alg>_init(state: *mut [u8; 192])`. -/
def initSig : Sig where
  params := [("state", .array true .u8 192)]

/-- Makes the streaming state at `state` represent the empty message, hashed
from `iv`, the initial hash value of `<alg>` (`H0_384`, `H0_512`,
`H0_512_224` or `H0_512_256`). -/
def initContract {M : ISA} (A : Abi M) (iv : HashValue) : Contract M :=
  initSig.contract A (post := fun state _ m' _ => Repr iv m' state [])

/-- `name`, which starts an `alg` computation from its initial hash value
`iv` (`H0_384`, `H0_512`, `H0_512_224` or `H0_512_256`, named `ivName`), on
every target. -/
def initApi (alg name ivName : String) (iv : HashValue) : Api where
  module := "sha512"
  name := name
  sig := initSig
  contracts := some fun A _ => initContract A iv
  summary := s!"Starts a {alg} computation: makes the SHA-512 streaming state `*state` represent \
    the empty message, hashed from the initial hash value of {alg} (`VG.Spec.Sha512.{ivName}`). \
    Continue with `vg_sha512_update` and `vg_sha512_finalize`.\n\n\
    Contract: `VG.Spec.Sha512.initContract` for `VG.Spec.Sha512.{ivName}`. The streaming state is \
    the hash value followed by a buffered partial block (`VG.Spec.Sha512.Repr`)."
  safety := []

def init384Api : Api := initApi "SHA-384" "vg_sha384_init" "H0_384" H0_384
def init512Api : Api := initApi "SHA-512" "vg_sha512_init" "H0_512" H0_512
def init512_224Api : Api := initApi "SHA-512/224" "vg_sha512_224_init" "H0_512_224" H0_512_224
def init512_256Api : Api := initApi "SHA-512/256" "vg_sha512_256_init" "H0_512_256" H0_512_256

/-- `vg_sha512_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize)`.
`count` is public. -/
def updateSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("data", .slice false .u8 "len")]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `msg` followed by the `len` bytes at `data`, from the same one. -/
def updatePost (pb : Nat) : updateSig.Post pb := fun state count data len m m' _ =>
  ∀ iv msg, Repr iv m state msg → count = BitVec.ofNat 64 msg.length →
    Repr iv m' state (msg ++ bytesAt m data len.toNat)

/-- `updatePost`. The state and the data are secret. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (post := updatePost A.ptrBits) (stack := stack)

/-- `vg_sha512_update` on every target. -/
def updateApi : Api where
  module := "sha512"
  name := "vg_sha512_update"
  sig := updateSig
  contracts := some fun A stack => updateContract A stack
  summary := "Absorbs data into a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if the \
    streaming state `*state` represents a message of `count` bytes (modulo 2⁶⁴), it then \
    represents that message followed by the `len` bytes at `data`.\n\n\
    Contract: `VG.Spec.Sha512.updateContract`. Constant time: only the pointers, `count` and `len` \
    may affect timing, not the state or the data."
  safety := []

/-- `vg_sha512_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; 64])`.
`count` is public; `state` is left unspecified. -/
def finalizeSig : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("out", .array true .u8 64)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes, fewer than 2⁶⁴, hashed from the initial hash value `iv`, writes the
final hash value `H⁽ᴺ⁾` of `msg` from `iv` (64 bytes; `finalHash iv msg`) to
`out`. The digest of SHA-384, SHA-512/224 or SHA-512/256 is its first 48,
28 or 32 bytes. -/
def finalizePost (pb : Nat) : finalizeSig.Post pb := fun state count out m m' _ =>
  ∀ iv msg, Repr iv m state msg → msg.length < 2 ^ 64 → count = BitVec.ofNat 64 msg.length →
    bytesAt m' out 64 = finalHash iv msg

/-- `finalizePost`. The state is secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A (post := finalizePost A.ptrBits) (stack := stack)

/-- `vg_sha512_finalize` on every target. -/
def finalizeApi : Api where
  module := "sha512"
  name := "vg_sha512_finalize"
  sig := finalizeSig
  contracts := some fun A stack => finalizeContract A stack
  summary := "Finishes a SHA-384, SHA-512, SHA-512/224 or SHA-512/256 computation: if the \
    streaming state `*state` represents a message of `count` bytes, hashed from an initial hash \
    value, writes the final hash value `H⁽ᴺ⁾` of that message (64 bytes) to `*out`. The SHA-512 \
    digest is all of it; the SHA-384, SHA-512/224 and SHA-512/256 digests are its first 48, 28 and \
    32 bytes.\n\n\
    Contract: `VG.Spec.Sha512.finalizeContract`. Constant time: only the pointers and `count` may \
    affect timing, not the state."
  safety := [
    "`count` must be the exact length of the message: messages of 2⁶⁴ bytes or more are not \
      supported.",
    "The contents of `state` on return are unspecified."]

/-- `vg_<alg>_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; D])`,
for a member of the family with a `D`-byte digest. `count` is public;
`state` is left unspecified. -/
def finalizeDigestSig (D : Nat) : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("out", .array true .u8 D)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes, fewer than 2⁶⁴, hashed from the initial hash value `iv`, writes
`digest msg` (`D` bytes) to `out`: for `<alg>`'s initial hash value, its
digest. -/
def finalizeDigestPost (iv : HashValue) (D : Nat) (digest : List Byte → List Byte) (pb : Nat) :
    (finalizeDigestSig D).Post pb := fun state count out m m' _ =>
  ∀ msg, Repr iv m state msg → msg.length < 2 ^ 64 → count = BitVec.ofNat 64 msg.length →
    bytesAt m' out D = digest msg

/-- `finalizeDigestPost`. The state is secret. -/
def finalizeDigestContract {M : ISA} (A : Abi M) (iv : HashValue) (D : Nat) (digest : List Byte → List Byte)
    (stack : Nat := 0) : Contract M :=
  (finalizeDigestSig D).contract A (post := finalizeDigestPost iv D digest A.ptrBits) (stack := stack)

/-- `name`, which finishes an `alg` computation started by `initName` from
its initial hash value `iv` (named `ivName`) with its digest `digest` (`D`
bytes, named `digestName`), on every target. -/
def finalizeDigestApi (alg name initName ivName digestName : String) (iv : HashValue) (D : Nat)
    (digest : List Byte → List Byte) : Api where
  module := "sha512"
  name := name
  sig := finalizeDigestSig D
  contracts := some fun A stack => finalizeDigestContract A iv D digest stack
  summary := s!"Finishes a {alg} computation: if the streaming state `*state` represents a message \
    of `count` bytes, hashed from the initial hash value of {alg} (as `{initName}` starts it), \
    writes the {alg} digest of that message ({D} bytes, `VG.Spec.Sha512.{digestName}`) to \
    `*out`.\n\n\
    Contract: `VG.Spec.Sha512.finalizeDigestContract` for `VG.Spec.Sha512.{ivName}` and \
    `VG.Spec.Sha512.{digestName}`. Constant time: only the pointers and `count` may affect timing, \
    not the state."
  safety := [
    "`count` must be the exact length of the message: messages of 2⁶⁴ bytes or more are not \
      supported.",
    "The contents of `state` on return are unspecified."]

def finalize384Api : Api :=
  finalizeDigestApi "SHA-384" "vg_sha384_finalize" "vg_sha384_init" "H0_384" "sha384" H0_384 48 sha384
def finalize512_224Api : Api :=
  finalizeDigestApi "SHA-512/224" "vg_sha512_224_finalize" "vg_sha512_224_init" "H0_512_224" "sha512_224"
    H0_512_224 28 sha512_224
def finalize512_256Api : Api :=
  finalizeDigestApi "SHA-512/256" "vg_sha512_256_finalize" "vg_sha512_256_init" "H0_512_256" "sha512_256"
    H0_512_256 32 sha512_256

/-- `vg_<alg>_digest(data: *const u8, len: usize, out: *mut [u8; D])`, for a
member of the family with a `D`-byte digest: the whole computation in one
call, with no streaming state. -/
def digestSig (D : Nat) : Sig where
  params := [("data", .slice false .u8 "len"), ("out", .array true .u8 D)]

/-- Writes `digest` of the `len` bytes at `data` (`D` bytes) to `out`. A
message in memory is shorter than 2⁶⁴ bytes on every target. -/
def digestPost (D : Nat) (digest : List Byte → List Byte) (pb : Nat) : (digestSig D).Post pb :=
  fun data len out m m' _ => bytesAt m' out D = digest (bytesAt m data len.toNat)

/-- `digestPost`. The data is secret. -/
def digestContract {M : ISA} (A : Abi M) (D : Nat) (digest : List Byte → List Byte)
    (stack : Nat := 0) : Contract M :=
  (digestSig D).contract A (post := digestPost D digest A.ptrBits) (stack := stack)

/-- `name`, which computes the `alg` digest `digest` (`D` bytes, named
`digestName`) of a message in one call, on every target. -/
def digestApi (alg name digestName : String) (D : Nat) (digest : List Byte → List Byte) : Api where
  module := "sha512"
  name := name
  sig := digestSig D
  contracts := some fun A stack => digestContract A D digest stack
  summary := s!"Computes the {alg} digest of the `len` bytes at `data` ({D} bytes, \
    `VG.Spec.Sha512.{digestName}`) and writes it to `*out`, in one call: the same result as \
    starting, updating and finishing a {alg} computation with that message.\n\n\
    Contract: `VG.Spec.Sha512.digestContract` for `VG.Spec.Sha512.{digestName}`. Constant time: \
    only the pointers and `len` may affect timing, not the data."
  safety := []

def digest384Api : Api := digestApi "SHA-384" "vg_sha384_digest" "sha384" 48 sha384
def digest512Api : Api := digestApi "SHA-512" "vg_sha512_digest" "sha512" 64 sha512
def digest512_224Api : Api := digestApi "SHA-512/224" "vg_sha512_224_digest" "sha512_224" 28 sha512_224
def digest512_256Api : Api := digestApi "SHA-512/256" "vg_sha512_256_digest" "sha512_256" 32 sha512_256

end VG.Spec.Sha512
