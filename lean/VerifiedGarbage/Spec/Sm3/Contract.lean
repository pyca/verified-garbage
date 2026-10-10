import VerifiedGarbage.Spec.Sm3
import VerifiedGarbage.TCB.Artifact

/-!
# SM3: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the compression
function and of streaming SM3 (`init`/`update`/`finalize`, on the
representation `Repr`), in terms of `Spec/Sm3.lean`, for any target:
`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and lengths are public (see `TCB/Sig.lean`); the contracts add
the postconditions and which other arguments are public. `update` and
`finalize` may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`), to pass arguments to the code they
inline.

`update` and `finalize` take the number of bytes of stack below the stack
pointer that an implementation's calls and frames use (`stack`, see
`Sig.contract`), 0 for one that uses none: it depends on the target, and on
which functions the implementation calls. They keep their working space
there. (Unlike SHA-256's and MD5's, they have no `_scratch` forms: nothing
calls SM3 with working space of its own.)
-/

namespace VG.Spec.Sm3

/-- `vg_sm3_compress(state: *mut [u32; 8], blocks: *const [u8; 64], n: usize, scratch: *mut [u64; 72])`.
`scratch` is working space: room for a block's whole message expansion
(`W_0 … W_67` and `W'_0 … W'_63`, 528 bytes) and six saved callee-saved
registers. The streaming functions pass theirs to it. -/
def compressSig : Sig where
  params := [("state", .array true .u32 8), ("blocks", .slice false (.array .u8 64) "n"),
    ("scratch", .array true .u64 72)]

/-- Updates the hash value at `state` with the `n` 64-byte blocks at
`blocks`. The hash value and the blocks are secret. -/
def compressContract {M : ISA} (A : Abi M) : Contract M :=
  compressSig.contract A (post := fun state blocks n _scratch m m' _ =>
    stateAt m' state = compressBlocks (stateAt m state) m blocks n.toNat)

/-- `vg_sm3_compress` on every target. -/
def compressApi : Api where
  module := "sm3"
  name := "vg_sm3_compress"
  sig := compressSig
  contracts := some fun A _ => compressContract A
  summary := "The SM3 compression function (GB/T 32905-2016, draft-sca-cfrg-sm3-02 §5.3): \
    updates the hash value `*state` (`A … H`) with the `n` 64-byte blocks starting at \
    `blocks`, in order.\n\n\
    Contract: `VG.Spec.Sm3.compressContract`. Constant time: only the pointers and `n` may \
    affect timing, not the hash value or the blocks."
  safety := ["The contents of `scratch` on return are unspecified."]

/-- `vg_sm3_init(state: *mut [u8; 96])`. -/
def initSig : Sig where
  params := [("state", .array true .u8 96)]

/-- Makes the streaming state at `state` represent the empty message. -/
def initContract {M : ISA} (A : Abi M) : Contract M :=
  initSig.contract A (post := fun state _ m' _ => Repr m' state [])

/-- `vg_sm3_init` on every target. -/
def initApi : Api where
  module := "sm3"
  name := "vg_sm3_init"
  sig := initSig
  contracts := some fun A _ => initContract A
  summary := "Starts an SM3 computation: makes the streaming state `*state` represent the empty \
    message.\n\n\
    Contract: `VG.Spec.Sm3.initContract`. The streaming state is the hash value followed by a \
    buffered partial block (`VG.Spec.Sm3.Repr`)."
  safety := []

/-- `vg_sm3_update(state: *mut [u8; 96], count: u64, data: *const u8, len: usize)`.
`count` is public. -/
def updateSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("data", .slice false .u8 "len")]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), then afterwards it represents `msg` followed by the `len`
bytes at `data`. -/
def updatePost (pb : Nat) : updateSig.Post pb := fun state count data len m m' _ =>
  ∀ msg, Repr m state msg → count = BitVec.ofNat 64 msg.length →
    Repr m' state (msg ++ bytesAt m data len.toNat)

/-- `updatePost`. The state and the data are secret. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (post := updatePost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_sm3_update` on every target. -/
def updateApi : Api where
  module := "sm3"
  name := "vg_sm3_update"
  sig := updateSig
  writeArgs := true
  contracts := some fun A stack => updateContract A stack
  summary := "Absorbs data into an SM3 computation: if the streaming state `*state` represents a \
    message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by the `len` \
    bytes at `data`.\n\n\
    Contract: `VG.Spec.Sm3.updateContract`. Constant time: only the pointers, `count` and `len` \
    may affect timing, not the state or the data."
  safety := []

/-- `vg_sm3_finalize(state: *mut [u8; 96], count: u64, out: *mut [u8; 32])`.
`count` is public; `state` is left unspecified. -/
def finalizeSig : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 32)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), the 32 bytes at `out` are afterwards the SM3 hash value
of `msg`. -/
def finalizePost (pb : Nat) : finalizeSig.Post pb := fun state count out m m' _ =>
  ∀ msg, Repr m state msg → count = BitVec.ofNat 64 msg.length → bytesAt m' out 32 = hash msg

/-- `finalizePost`. The state is secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A (post := finalizePost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_sm3_finalize` on every target. -/
def finalizeApi : Api where
  module := "sm3"
  name := "vg_sm3_finalize"
  sig := finalizeSig
  writeArgs := true
  contracts := some fun A stack => finalizeContract A stack
  summary := "Finishes an SM3 computation: if the streaming state `*state` represents a message \
    of `count` bytes (modulo 2⁶⁴), writes the SM3 hash value of that message (32 bytes) to \
    `*out`.\n\n\
    Contract: `VG.Spec.Sm3.finalizeContract`. Constant time: only the pointers and `count` may \
    affect timing, not the state."
  safety := ["The contents of `state` on return are unspecified."]

end VG.Spec.Sm3
