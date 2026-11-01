module

public import VerifiedGarbage.Spec.Md5
public import VerifiedGarbage.TCB.Artifact

/-!
# MD5: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of streaming MD5
(`init`/`update`/`finalize`, on the representation `Repr`), in terms of
`Spec/Md5.lean`, for any target:
`A` is the target's calling convention. The signatures fix where the
arguments are, the memory each function may access, disjointness, and that
the pointers and lengths are public (see `TCB/Sig.lean`); the contracts add
the postconditions and which other arguments are public. `update` and
`finalize` may overwrite their arguments passed in memory, where the calling
convention allows it (`writeArgs`), to pass arguments to the code they
inline.

`update` and `finalize` take the number of bytes of stack below the stack pointer that
an implementation's calls and frames use (`stack`, see `Sig.contract`), 0 for
one that uses none: it depends on the target, and on which functions the
implementation calls. They keep their working space there.
-/

@[expose] public section

namespace VG.Spec.Md5

/-- `vg_md5_init(state: *mut [u8; 80])`. -/
def initSig : Sig where
  params := [("state", .array true .u8 80)]

/-- Makes the streaming state at `state` represent the empty message. -/
def initContract {M : ISA} (A : Abi M) : Contract M :=
  initSig.contract A (post := fun state _ m' _ => Repr m' state [])

/-- `vg_md5_init` on every target. -/
def initApi : Api where
  module := "md5"
  name := "vg_md5_init"
  sig := initSig
  contracts := some fun A _ => initContract A
  summary := "Starts an MD5 computation: makes the streaming state `*state` represent the empty \
    message.\n\n\
    Contract: `VG.Spec.Md5.initContract`. The streaming state is the MD buffer followed by a \
    buffered partial block (`VG.Spec.Md5.Repr`)."
  safety := []

/-- `vg_md5_update(state: *mut [u8; 80], count: u64, data: *const u8, len: usize)`.
`count` is public. -/
def updateSig : Sig where
  params := [("state", .array true .u8 80), ("count", .int .u64 true),
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

/-- `vg_md5_update` on every target. -/
def updateApi : Api where
  module := "md5"
  name := "vg_md5_update"
  sig := updateSig
  writeArgs := true
  contracts := some fun A stack => updateContract A stack
  summary := "Absorbs data into an MD5 computation: if the streaming state `*state` represents a \
    message of `count` bytes (modulo 2⁶⁴), it then represents that message followed by the `len` \
    bytes at `data`.\n\n\
    Contract: `VG.Spec.Md5.updateContract`. Constant time: only the pointers, `count` and `len` \
    may affect timing, not the state or the data."
  safety := []

/-- `vg_md5_finalize(state: *mut [u8; 80], count: u64, out: *mut [u8; 16])`.
`count` is public; `state` is left unspecified. -/
def finalizeSig : Sig where
  params := [("state", .array true .u8 80), ("count", .int .u64 true),
    ("out", .array true .u8 16)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), the 16 bytes at `out` are afterwards the MD5 digest of
`msg`. -/
def finalizePost (pb : Nat) : finalizeSig.Post pb := fun state count out m m' _ =>
  ∀ msg, Repr m state msg → count = BitVec.ofNat 64 msg.length → bytesAt m' out 16 = hash msg

/-- `finalizePost`. The state is secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  finalizeSig.contract A (post := finalizePost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_md5_finalize` on every target. -/
def finalizeApi : Api where
  module := "md5"
  name := "vg_md5_finalize"
  sig := finalizeSig
  writeArgs := true
  contracts := some fun A stack => finalizeContract A stack
  summary := "Finishes an MD5 computation: if the streaming state `*state` represents a message of \
    `count` bytes (modulo 2⁶⁴), writes the MD5 digest of that message to `*out`.\n\n\
    Contract: `VG.Spec.Md5.finalizeContract`. Constant time: only the pointers and `count` may \
    affect timing, not the state."
  safety := ["The contents of `state` on return are unspecified."]

end VG.Spec.Md5
