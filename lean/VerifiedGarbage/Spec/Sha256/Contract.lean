module

public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.TCB.Artifact

/-!
# SHA-256: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of streaming SHA-224
and SHA-256 (`init`/`update`/`finalize`, on the representation `ReprFrom`),
in terms of `Spec/Sha256.lean`, for any target:
`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and lengths are public (see `TCB/Sig.lean`); the contracts add
the postconditions and which other arguments are public. `update` and
`finalize` (not `finalize224`) may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`), to pass arguments to the code they
inline.

SHA-224 and SHA-256 share `update` and `finalize`, which hold for a state
hashed from any initial hash value; each has its own `init`. SHA-224's own
`finalize` (`finalize224Api`) writes its digest, the whole result of
FIPS 180-4 §6.3. `digest` (`digestApi`) computes SHA-224's or SHA-256's
digest of a message in memory in one call, with no streaming state.

`update`, `finalize` and `digest` take the number of bytes of stack below the stack pointer that
an implementation's calls and frames use (`stack`, see `Sig.contract`), 0 for
one that uses none: it depends on the target, and on which functions the
implementation calls. They keep their working space there.
-/

@[expose] public section

namespace VG.Spec.Sha256

/-- `vg_sha256_init(state: *mut [u8; 96])`. -/
def initSig : Sig where
  params := [("state", .array true .u8 96)]

/-- Makes the streaming state at `state` represent the empty message. -/
def initContract {M : ISA} (A : Abi M) : Contract M :=
  initSig.contract A (post := fun state _ m' _ => Repr m' state [])

/-- `vg_sha256_init` on every target. -/
def initApi : Api where
  module := "sha256"
  name := "vg_sha256_init"
  sig := initSig
  contracts := some fun A _ => initContract A
  summary := "Starts a SHA-256 computation: makes the streaming state `*state` represent the empty \
    message.\n\n\
    Contract: `VG.Spec.Sha256.initContract`. The streaming state is the hash value followed by a \
    buffered partial block (`VG.Spec.Sha256.Repr`)."
  safety := []

/-- `vg_sha224_init(state: *mut [u8; 96])`, with `vg_sha256_init`'s signature
(`initSig`): makes the streaming state at `state` represent the empty message,
hashed from SHA-224's initial hash value `H0_224`. -/
def init224Contract {M : ISA} (A : Abi M) : Contract M :=
  initSig.contract A (post := fun state _ m' _ => ReprFrom H0_224 m' state [])

/-- `vg_sha224_init` on every target. -/
def init224Api : Api where
  module := "sha256"
  name := "vg_sha224_init"
  sig := initSig
  contracts := some fun A _ => init224Contract A
  summary := "Starts a SHA-224 computation: makes the SHA-256 streaming state `*state` represent \
    the empty message, hashed from the initial hash value of SHA-224 \
    (`VG.Spec.Sha256.H0_224`). Continue with `vg_sha256_update` and `vg_sha256_finalize`, and \
    take the first 28 bytes of the final hash value as the digest.\n\n\
    Contract: `VG.Spec.Sha256.init224Contract`. The streaming state is the hash value followed by \
    a buffered partial block (`VG.Spec.Sha256.ReprFrom`)."
  safety := []

/-- `vg_sha256_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize)`.
`count` is public. -/
def updateSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("data", .slice false .u8 "len")]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), hashed from any initial hash value, then afterwards it
represents `msg` followed by the `len` bytes at `data`, from the same one. -/
def updatePost (pb : Nat) : updateSig.Post pb := fun state count data len m m' _ =>
  ∀ iv msg, ReprFrom iv m state msg → count = BitVec.ofNat 64 msg.length →
    ReprFrom iv m' state (msg ++ bytesAt m data len.toNat)

/-- `updatePost`. The state and the data are secret. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (post := updatePost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_sha256_update` on every target. -/
def updateApi : Api where
  module := "sha256"
  name := "vg_sha256_update"
  sig := updateSig
  writeArgs := true
  contracts := some fun A stack => updateContract A stack
  summary := "Absorbs data into a SHA-224 or SHA-256 computation: if the streaming state `*state` \
    represents a message of `count` bytes (modulo 2⁶⁴), it then represents that message followed \
    by the `len` bytes at `data`.\n\n\
    Contract: `VG.Spec.Sha256.updateContract`. Constant time: only the pointers, `count` and `len` \
    may affect timing, not the state or the data."
  safety := []

/-- `vg_sha256_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32])`.
`count` is public; `state` is left unspecified. -/
def finalizeSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 32)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), hashed from the initial hash value `iv`, writes the final
hash value `H⁽ᴺ⁾` of `msg` from `iv` (32 bytes; `finalHash iv msg`) to `out`:
the SHA-256 digest of `msg` if `iv` is `H0`, and the SHA-224 digest followed
by four more bytes if `iv` is `H0_224`. -/
def finalizePost (pb : Nat) : finalizeSig.Post pb := fun state count out m m' _ =>
  ∀ iv msg, ReprFrom iv m state msg → count = BitVec.ofNat 64 msg.length →
    bytesAt m' out 32 = finalHash iv msg

/-- `finalizePost`. The state is secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A (post := finalizePost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_sha256_finalize` on every target. -/
def finalizeApi : Api where
  module := "sha256"
  name := "vg_sha256_finalize"
  sig := finalizeSig
  writeArgs := true
  contracts := some fun A stack => finalizeContract A stack
  summary := "Finishes a SHA-224 or SHA-256 computation: if the streaming state `*state` \
    represents a message of `count` bytes (modulo 2⁶⁴), hashed from an initial hash value, writes \
    the final hash value `H⁽ᴺ⁾` of that message (32 bytes) to `*out`. The SHA-256 digest is all of \
    it; the SHA-224 digest is its first 28 bytes.\n\n\
    Contract: `VG.Spec.Sha256.finalizeContract`. Constant time: only the pointers and `count` may \
    affect timing, not the state."
  safety := ["The contents of `state` on return are unspecified."]

/-- `vg_sha224_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 28])`.
`count` is public; `state` is left unspecified. -/
def finalize224Sig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 28)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), hashed from SHA-224's initial hash value `H0_224`, writes
the SHA-224 digest of `msg` (28 bytes; `sha224 msg`) to `out`. -/
def finalize224Post (pb : Nat) : finalize224Sig.Post pb := fun state count out m m' _ =>
  ∀ msg, ReprFrom H0_224 m state msg → count = BitVec.ofNat 64 msg.length →
    bytesAt m' out 28 = sha224 msg

/-- `finalize224Post`. The state is secret. -/
def finalize224Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalize224Sig.contract A (post := finalize224Post A.ptrBits) (stack := stack)

/-- `vg_sha224_finalize` on every target. -/
def finalize224Api : Api where
  module := "sha256"
  name := "vg_sha224_finalize"
  sig := finalize224Sig
  contracts := some fun A stack => finalize224Contract A stack
  summary := "Finishes a SHA-224 computation: if the streaming state `*state` represents a message \
    of `count` bytes (modulo 2⁶⁴), hashed from the initial hash value of SHA-224 (as \
    `vg_sha224_init` starts it), writes the SHA-224 digest of that message (28 bytes, \
    `VG.Spec.Sha256.sha224`) to `*out`.\n\n\
    Contract: `VG.Spec.Sha256.finalize224Contract`. Constant time: only the pointers and `count` \
    may affect timing, not the state."
  safety := ["The contents of `state` on return are unspecified."]

/-- `vg_<alg>_digest(data: *const u8, len: usize, out: *mut [u8; D])`, for
SHA-224 or SHA-256 with a `D`-byte digest: the whole computation in one
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
  module := "sha256"
  name := name
  sig := digestSig D
  contracts := some fun A stack => digestContract A D digest stack
  summary := s!"Computes the {alg} digest of the `len` bytes at `data` ({D} bytes, \
    `VG.Spec.Sha256.{digestName}`) and writes it to `*out`, in one call: the same result as \
    starting, updating and finishing a {alg} computation with that message.\n\n\
    Contract: `VG.Spec.Sha256.digestContract` for `VG.Spec.Sha256.{digestName}`. Constant time: \
    only the pointers and `len` may affect timing, not the data."
  safety := []

def digest224Api : Api := digestApi "SHA-224" "vg_sha224_digest" "sha224" 28 sha224
def digest256Api : Api := digestApi "SHA-256" "vg_sha256_digest" "hash" 32 hash

end VG.Spec.Sha256
