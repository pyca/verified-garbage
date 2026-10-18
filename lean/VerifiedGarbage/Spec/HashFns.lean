module

public import VerifiedGarbage.Spec.HashId
public import VerifiedGarbage.Spec.Hmac.Generic

/-!
# Hash functions passed as tables of their streaming functions

**Trusted** (as every file in `Spec/`). A function that takes a hash
function as an argument takes its number (`HashId`) and a pointer to a
table of three words, the addresses of the hash function's streaming
`init`, `update` and `finalize` (`*const [u64; 3]`), which it calls
(`Code.icall`): whichever implementation the caller chose for the CPU
(e.g. `vg_sha256_update_scratch_shani`), with no copy of the caller for each
hash function or implementation.

A hash function's streaming functions (`Streaming`) are its streaming
state's representation and size (`Hmac.StreamingHash`), the number of bytes
`finalize` writes (the digest, then any more bytes of the final hash value),
and the 64-bit words of working space `update` and `finalize` take. They
have the shapes of the `_scratch` functions of each hash function's own
contracts (e.g. `vg_sha256_update_scratch`, `Spec/Sha256/Contract.lean`),
whose contracts imply these:

* `init(state: *mut [u8; S])` (`initContract`): the state represents the
  empty message;
* `update(state: *mut [u8; S], count: u64, data: *const u8, len: usize,
  scratch: *mut [u64; W])` (`updateContract`): absorbs `data` into a state
  representing `count` bytes;
* `finalize(state: *mut [u8; S], count: u64, out: *mut [u8; F],
  scratch: *mut [u64; W])` (`finalizeContract`): writes `F` bytes whose
  first are the digest of the message the state represents.

`streaming i` is the hash function the number `i` names, with its sizes:
MD5, SHA-1 and the SHA-2 functions (0 to 7). SHA-224 is SHA-256's state
from SHA-224's initial hash value (`vg_sha224_init`, then SHA-256's `update`
and `finalize`, whose first 28 bytes are the digest), and the SHA-512
family's members share SHA-512's `update` and `finalize` likewise.

`table T m p meets` says the table at `p` in the memory `m` holds `T`'s
streaming functions: each word is the address of a function that meets
(`meets`, `FnMeets` in a contract's precondition: `Sig.contract`'s `fns`)
its contract with `fnStack` bytes of stack below its return address. A
contract taking the hash function `i` and the table `p` requires
`tableOf i m p meets`.
-/

@[expose] public section

namespace VG.Spec.HashFns

open Sha256 (bytesAt)
open Hmac (StreamingHash)

/-- A hash function's streaming functions: its streaming state, the bytes
`finalize` writes, which begin with the digest, and the 64-bit words of
working space of `update` and `finalize`. -/
structure Streaming where
  S : StreamingHash
  outBytes : Nat
  scratch : Nat

variable (T : Streaming)

/-- `init(state: *mut [u8; S])`. -/
def initSig : Sig where
  params := [("state", .array true .u8 T.S.stateBytes)]

/-- Makes the streaming state at `state` represent the empty message. -/
def initPost (pb : Nat) : (initSig T).Post pb := fun state _ m' _ => T.S.Repr m' state []

/-- `initPost`. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (initSig T).contract A (post := initPost T A.ptrBits) (stack := stack)

/-- `update(state: *mut [u8; S], count: u64, data: *const u8, len: usize,
scratch: *mut [u64; W])`. `count` is public. -/
def updateSig : Sig where
  params := [("state", .array true .u8 T.S.stateBytes), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 T.scratch)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes (modulo 2⁶⁴), it then represents `msg` followed by the `len` bytes at
`data`. -/
def updatePost (pb : Nat) : (updateSig T).Post pb := fun state count data len _scratch m m' _ =>
  ∀ msg, T.S.Repr m state msg → count = BitVec.ofNat 64 msg.length →
    T.S.Repr m' state (msg ++ bytesAt m data len.toNat)

/-- `updatePost`. The state and the data are secret. -/
def updateContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (updateSig T).contract A (post := updatePost T A.ptrBits) (writeArgs := true) (stack := stack)

/-- `finalize(state: *mut [u8; S], count: u64, out: *mut [u8; F],
scratch: *mut [u64; W])`. `count` is public; `state` is left unspecified. -/
def finalizeSig : Sig where
  params := [("state", .array true .u8 T.S.stateBytes), ("count", .int .u64 true),
    ("out", .array true .u8 T.outBytes), ("scratch", .array true .u64 T.scratch)]

/-- If the streaming state at `state` represents a message `msg` of `count`
bytes, fewer than 2⁶⁴, the first bytes of the `F` it writes to `out` are the
digest of `msg`. -/
def finalizePost (pb : Nat) : (finalizeSig T).Post pb := fun state count out _scratch m m' _ =>
  ∀ msg, T.S.Repr m state msg → msg.length < 2 ^ 64 → count = BitVec.ofNat 64 msg.length →
    (bytesAt m' out T.outBytes).take T.S.digestBytes = T.S.H.hash msg

/-- `finalizePost`. The state is secret. -/
def finalizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (finalizeSig T).contract A (post := finalizePost T A.ptrBits) (writeArgs := true) (stack := stack)

/-- The bytes of stack below its return address that each function of a
table may use (for a call of its compression function). -/
def fnStack : Nat := 8

/-- The table at `p` in `m` holds `T`'s streaming functions: the addresses
of functions meeting `initContract`, `updateContract` and `finalizeContract`
with `fnStack` bytes of stack, in this order. -/
def table {M : ISA} (m : Mem) (p : Addr) (meets : Addr → (Abi M → Nat → Contract M) → Nat → Prop) :
    Prop :=
  meets (m.readW p 64) (fun A n => initContract T A n) fnStack ∧
    meets (m.readW (p + 8) 64) (fun A n => updateContract T A n) fnStack ∧
    meets (m.readW (p + 16) 64) (fun A n => finalizeContract T A n) fnStack

/-- The table's words, which a function calling its functions makes public
(its contract's `leak`): the addresses it calls. -/
def tableWords (m : Mem) (p : Addr) : List Nat :=
  [(m.readW p 64).toNat, (m.readW (p + 8) 64).toNat, (m.readW (p + 16) 64).toNat]

/-- The streaming functions of the hash function the number `i` names
(`HashId.mgf1`), for MD5, SHA-1 and the SHA-2 functions: the sizes of
`vg_<hash>_update_scratch` and `vg_<hash>_finalize_scratch`. -/
def streaming : Nat → Option Streaming
  | 0 => some ⟨Hmac.md5S, 16, 14⟩
  | 1 => some ⟨Hmac.sha1S, 20, 20⟩
  | 2 => some ⟨Hmac.sha224S, 32, 76⟩
  | 3 => some ⟨Hmac.sha256S, 32, 76⟩
  | 4 => some ⟨Hmac.sha384S, 64, 172⟩
  | 5 => some ⟨Hmac.sha512S, 64, 172⟩
  | 6 => some ⟨Hmac.sha512_224S, 64, 172⟩
  | 7 => some ⟨Hmac.sha512_256S, 64, 172⟩
  | _ => none

/-- The table at `p` in `m` holds the streaming functions of the hash
function `i` names. -/
def tableOf {M : ISA} (i : Nat) (m : Mem) (p : Addr)
    (meets : Addr → (Abi M → Nat → Contract M) → Nat → Prop) : Prop :=
  match streaming i with
  | some T => table T m p meets
  | none => False

/-- The `# Safety` item on the table `fns` of the hash function `hash`
names. -/
def tableSafety (fns hash : String) : String :=
  s!"`{fns}` must point to the addresses of the streaming `init`, `update` and `finalize` \
    of the hash function `{hash}` names, as `vg_<hash>_init`, `vg_<hash>_update_scratch` and \
    `vg_<hash>_finalize_scratch` (`VG.Spec.HashFns.streaming`), in this order: functions \
    generated by this crate and verified against `VG.Spec.HashFns.initContract`, \
    `updateContract` and `finalizeContract`, with {fnStack} bytes of stack, for the CPU's \
    features (e.g. any variant of `vg_sha256_update_scratch` the CPU can run)."

end VG.Spec.HashFns
