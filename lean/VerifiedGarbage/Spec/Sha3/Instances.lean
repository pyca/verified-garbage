module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.TCB.Artifact

/-!
# SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128 and SHAKE256: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of the six functions of
FIPS 202 (§6), each streamed by functions of its own, in terms of
`Spec/Sha3.lean`, for any target: `A` is the target's calling convention.
The signatures fix where the arguments are, the memory each function may
access, disjointness, and that the pointers and lengths are public (see
`TCB/Sig.lean`); the contracts add the postconditions and which other
arguments are public. The state and the message are secret; the position
within the block is public.

Unlike the sponge's functions (`Spec/Sha3/Contract.lean`), which take the
rate and the domain-separation suffix as arguments, each function here has
its own rate and suffix in its code: the postconditions of the last
functions name the function of FIPS 202 that is computed (`sha3_256`,
`shake128`, …), so the result of a computation does not depend on the
caller passing the right constants.

A computation of `F` starts from the all-zero state, which represents the
empty message for every rate (`Repr`), at position 0; `vg_<f>_update`
absorbs each piece of the message, from the position the previous call
returned. Then:

* for SHA3-224/256/384/512, `vg_<f>_finalize` writes the digest `F(M)`;
* for SHAKE128 and SHAKE256, `vg_<f>_finalize` pads the message, leaving a
  state that continues `F(M, d)` from its first byte on, at position 0
  (`XofRepr`), and each call of `vg_<f>_squeeze`, from the state and position
  the previous one left, writes the bytes of `F(M, d)` that follow.

The rate of the representation (`Repr`) shared by a function's `update` and
its other functions is its sponge's (§6): `update` and the others are proven
for the same `rate`, and the others' postconditions name the function of
FIPS 202, so a computation gives that function's output however it is split.

The functions take the number of bytes of stack below the stack pointer that
an implementation's calls and frames use (`stack`, see `Sig.contract`), 0
for one that uses none: it depends on the target. They may overwrite their
arguments passed in memory, where the calling convention allows it
(`writeArgs`). `scratch` is `update`'s working space, sized for the target
with the fewest registers (the Rust sponge keeps it on its stack); the other
functions keep theirs on the stack.
-/

@[expose] public section

namespace VG.Spec.Sha3

/-- A hash function of FIPS 202 (§6.1), streamed: its name, the name of its
Rust functions (`vg_<rust>_update`, `vg_<rust>_finalize`), the rate of its
sponge in bytes (`(1600 - c) / 8` for its capacity `c`), the length of its
digest in bytes, and the function. -/
structure HashFn where
  name : String
  rust : String
  rate : Nat
  len : Nat
  digest : List Byte → List Byte

/-- `SHA3-224 = KECCAK[448]`, so `r = (1600 - 448) / 8`. -/
def hashSha3_224 : HashFn := ⟨"SHA3-224", "sha3_224", 144, 28, sha3_224⟩
/-- `SHA3-256 = KECCAK[512]`. -/
def hashSha3_256 : HashFn := ⟨"SHA3-256", "sha3_256", 136, 32, sha3_256⟩
/-- `SHA3-384 = KECCAK[768]`. -/
def hashSha3_384 : HashFn := ⟨"SHA3-384", "sha3_384", 104, 48, sha3_384⟩
/-- `SHA3-512 = KECCAK[1024]`. -/
def hashSha3_512 : HashFn := ⟨"SHA3-512", "sha3_512", 72, 64, sha3_512⟩

/-- An extendable-output function of FIPS 202 (§6.2), streamed: its name, the
name of its Rust functions (`vg_<rust>_update`, `vg_<rust>_finalize`,
`vg_<rust>_squeeze`), the rate of its sponge in bytes, and the function,
of the message and the number of bytes of output. -/
structure Xof where
  name : String
  rust : String
  rate : Nat
  xof : List Byte → Nat → List Byte

/-- `SHAKE128 = KECCAK[256]`, so `r = (1600 - 256) / 8`. -/
def xofShake128 : Xof := ⟨"SHAKE128", "shake128", 168, shake128⟩
/-- `SHAKE256 = KECCAK[512]`. -/
def xofShake256 : Xof := ⟨"SHAKE256", "shake256", 136, shake256⟩

/-- The state at `p`, squeezed from byte `pos` of its output on, continues
the output of `xof msg` after its first `n` bytes: for every `d`, its next
`d` bytes are bytes `n … n + d - 1` of `xof msg (n + d)`. -/
def XofRepr (mem : Mem) (p : Addr) (rate pos : Nat) (xof : List Byte → Nat → List Byte)
    (msg : List Byte) (n : Nat) : Prop :=
  ∀ d, squeezeFrom rate (stateAt mem p) pos d = (xof msg (n + d)).drop n

/-! ## Absorbing -/

/-- `vg_<f>_update(state: *mut [u64; 25], pos: usize, data: *const u8, len: usize, scratch: *mut [u64; 80]) -> usize`.
`pos` is public. -/
def updateSig : Sig where
  params := [("state", .array true .u64 25), ("pos", .int .usize true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 80)]
  ret := some .usize

/-- `pos < rate`. -/
def updatePre (rate pb : Nat) : Curry (updateSig.words pb) (Mem → Prop) :=
  fun _state pos _data _len _scratch _ => pos.toNat < rate

/-- If the state at `state` represents a message `msg` for `rate`, and `pos`
is the length of `msg` modulo `rate`, then afterwards it represents `msg`
followed by the `len` bytes at `data`. Returns `(pos + len) mod rate`, the
position after them. Whatever `scratch` is. -/
def updatePost (rate pb : Nat) : updateSig.Post pb := fun state pos data len _scratch m m' ret =>
  (∀ msg, Repr m state rate msg → pos.toNat = msg.length % rate →
    Repr m' state rate (msg ++ bytesAt m data len.toNat)) ∧
  ret.toNat = (pos.toNat + len.toNat) % rate

/-- `updatePre` and `updatePost`, for the rate `rate`. -/
def updateContract {M : ISA} (A : Abi M) (rate : Nat) (stack : Nat := 0) : Contract M :=
  updateSig.contract A (pre := updatePre rate A.ptrBits) (post := updatePost rate A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_<rust>_update`, which absorbs data into a computation of `name`, with
the rate `rate`, on every target. -/
def updateApi (name rust : String) (rate : Nat) : Api where
  module := "sha3"
  name := s!"vg_{rust}_update"
  sig := updateSig
  writeArgs := true
  contracts := some fun A stack => updateContract A rate stack
  summary := s!"Absorbs data into a {name} computation: if the state `*state` represents a message \
    whose length is `pos` modulo {rate} (`VG.Spec.Sha3.Repr` with {name}'s rate, {rate}), it then \
    represents that message followed by the `len` bytes at `data`. Returns the position after them, \
    `(pos + len) % {rate}`. `*scratch` is its working space. A computation starts from the all-zero \
    state, at position 0.\n\n\
    Contract: `VG.Spec.Sha3.updateContract` with the rate {rate}. Constant time: only the pointers, \
    `pos` and `len` may affect timing, not the state or the data."
  safety := [
    s!"`pos` must be less than {rate}.",
    "The contents of `scratch` on return are unspecified."]

/-! ## SHA-3: the digest -/

/-- `vg_<f>_finalize(state: *mut [u64; 25], pos: usize, out: *mut [u8; D])`,
for a hash function with a `D`-byte digest. `pos` is public; `state` is left
unspecified. -/
def finalizeSig (D : Nat) : Sig where
  params := [("state", .array true .u64 25), ("pos", .int .usize true),
    ("out", .array true .u8 D)]

/-- `pos < H.rate`. -/
def finalizePre (H : HashFn) (pb : Nat) : Curry ((finalizeSig H.len).words pb) (Mem → Prop) :=
  fun _state pos _out _ => pos.toNat < H.rate

/-- If the state at `state` represents a message `msg` for `H`'s rate, and
`pos` is the length of `msg` modulo the rate, writes the digest of `msg`
(`H.len` bytes, `H.digest msg`) to `out`. -/
def finalizePost (H : HashFn) (pb : Nat) : (finalizeSig H.len).Post pb := fun state pos out m m' _ =>
  ∀ msg, Repr m state H.rate msg → pos.toNat = msg.length % H.rate →
    bytesAt m' out H.len = H.digest msg

/-- `finalizePre` and `finalizePost`. -/
def finalizeContract {M : ISA} (A : Abi M) (H : HashFn) (stack : Nat := 0) : Contract M :=
  (finalizeSig H.len).contract A (pre := finalizePre H A.ptrBits) (post := finalizePost H A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_<f>_finalize` for the hash function `H`, named `digestName` in
`Spec/Sha3.lean`, on every target. -/
def finalizeApi (H : HashFn) (digestName : String) : Api where
  module := "sha3"
  name := s!"vg_{H.rust}_finalize"
  sig := finalizeSig H.len
  writeArgs := true
  contracts := some fun A stack => finalizeContract A H stack
  summary := s!"Finishes a {H.name} computation: if the state `*state` represents a message whose \
    length is `pos` modulo {H.rate} (`VG.Spec.Sha3.Repr` with {H.name}'s rate, as \
    `vg_{H.rust}_update` leaves it), writes the {H.name} digest of that message ({H.len} bytes, \
    `VG.Spec.Sha3.{digestName}`) to `*out`.\n\n\
    Contract: `VG.Spec.Sha3.finalizeContract` for `VG.Spec.Sha3.hash{digestName.capitalize}`. \
    Constant time: only the pointers and `pos` may affect timing, not the state."
  safety := [
    s!"`pos` must be less than {H.rate}.",
    "The contents of `state` on return are unspecified."]

def updateSha3_224Api : Api := updateApi hashSha3_224.name hashSha3_224.rust hashSha3_224.rate
def updateSha3_256Api : Api := updateApi hashSha3_256.name hashSha3_256.rust hashSha3_256.rate
def updateSha3_384Api : Api := updateApi hashSha3_384.name hashSha3_384.rust hashSha3_384.rate
def updateSha3_512Api : Api := updateApi hashSha3_512.name hashSha3_512.rust hashSha3_512.rate
def finalizeSha3_224Api : Api := finalizeApi hashSha3_224 "sha3_224"
def finalizeSha3_256Api : Api := finalizeApi hashSha3_256 "sha3_256"
def finalizeSha3_384Api : Api := finalizeApi hashSha3_384 "sha3_384"
def finalizeSha3_512Api : Api := finalizeApi hashSha3_512 "sha3_512"

/-! ## SHAKE: padding and squeezing -/

/-- `vg_<f>_finalize(state: *mut [u64; 25], pos: usize)`, for an
extendable-output function. `pos` is public. -/
def xofFinalizeSig : Sig where
  params := [("state", .array true .u64 25), ("pos", .int .usize true)]

/-- `pos < X.rate`. -/
def xofFinalizePre (X : Xof) (pb : Nat) : Curry (xofFinalizeSig.words pb) (Mem → Prop) :=
  fun _state pos _ => pos.toNat < X.rate

/-- If the state at `state` represents a message `msg` for `X`'s rate, and
`pos` is the length of `msg` modulo the rate, then afterwards, squeezed from
position 0, it gives the output of `X.xof msg` from its first byte on. -/
def xofFinalizePost (X : Xof) (pb : Nat) : xofFinalizeSig.Post pb := fun state pos m m' _ =>
  ∀ msg, Repr m state X.rate msg → pos.toNat = msg.length % X.rate →
    XofRepr m' state X.rate 0 X.xof msg 0

/-- `xofFinalizePre` and `xofFinalizePost`. -/
def xofFinalizeContract {M : ISA} (A : Abi M) (X : Xof) (stack : Nat := 0) : Contract M :=
  xofFinalizeSig.contract A (pre := xofFinalizePre X A.ptrBits) (post := xofFinalizePost X A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_<f>_finalize` for the extendable-output function `X`, named `xofName`
in `Spec/Sha3.lean`, on every target. `update` names the function whose
states it finishes: `X`'s own, or, for SHAKE256, SHA3-256's, of the same
rate. -/
def xofFinalizeApi (X : Xof) (xofName : String) (update : String := s!"vg_{X.rust}_update") :
    Api where
  module := "sha3"
  name := s!"vg_{X.rust}_finalize"
  sig := xofFinalizeSig
  writeArgs := true
  contracts := some fun A stack => xofFinalizeContract A X stack
  summary := s!"Finishes absorbing a {X.name} message: if the state `*state` represents a message \
    whose length is `pos` modulo {X.rate} (`VG.Spec.Sha3.Repr` with {X.name}'s rate, as \
    `{update}` leaves it), it becomes a state that, squeezed by `vg_{X.rust}_squeeze` \
    from position 0, gives the output of {X.name} of that message (`VG.Spec.Sha3.{xofName}`) from \
    its first byte on (`VG.Spec.Sha3.XofRepr`).\n\n\
    Contract: `VG.Spec.Sha3.xofFinalizeContract` for `VG.Spec.Sha3.xof{xofName.capitalize}`. \
    Constant time: only the pointer and `pos` may affect timing, not the state."
  safety := [s!"`pos` must be less than {X.rate}."]

/-- `vg_<f>_squeeze(state: *mut [u64; 25], pos: usize, out: *mut u8, outlen: usize) -> usize`.
`pos` is public. -/
def xofSqueezeSig : Sig where
  params := [("state", .array true .u64 25), ("pos", .int .usize true),
    ("out", .slice true .u8 "outlen")]
  ret := some .usize

/-- `pos ≤ X.rate`. -/
def xofSqueezePre (X : Xof) (pb : Nat) : Curry (xofSqueezeSig.words pb) (Mem → Prop) :=
  fun _state pos _out _outlen _ => pos.toNat ≤ X.rate

/-- If the state at `state`, from position `pos`, continues the output of
`X.xof msg` after its first `n` bytes, writes the next `outlen` bytes of that
output to `out`, and leaves a state and returns a position (at most the
rate) that continue it after its first `n + outlen` bytes. -/
def xofSqueezePost (X : Xof) (pb : Nat) : xofSqueezeSig.Post pb :=
  fun state pos out outlen m m' ret =>
    (∀ msg n, XofRepr m state X.rate pos.toNat X.xof msg n →
      bytesAt m' out outlen.toNat = (X.xof msg (n + outlen.toNat)).drop n ∧
      XofRepr m' state X.rate ret.toNat X.xof msg (n + outlen.toNat)) ∧
    ret.toNat ≤ X.rate

/-- `xofSqueezePre` and `xofSqueezePost`. -/
def xofSqueezeContract {M : ISA} (A : Abi M) (X : Xof) (stack : Nat := 0) : Contract M :=
  xofSqueezeSig.contract A (pre := xofSqueezePre X A.ptrBits) (post := xofSqueezePost X A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_<f>_squeeze` for the extendable-output function `X`, named `xofName`
in `Spec/Sha3.lean`, on every target. -/
def xofSqueezeApi (X : Xof) (xofName : String) : Api where
  module := "sha3"
  name := s!"vg_{X.rust}_squeeze"
  sig := xofSqueezeSig
  writeArgs := true
  contracts := some fun A stack => xofSqueezeContract A X stack
  summary := s!"Squeezes {X.name} output: if the state `*state`, from position `pos`, continues the \
    output of {X.name} of a message (`VG.Spec.Sha3.{xofName}`) after its first `n` bytes \
    (`VG.Spec.Sha3.XofRepr`), writes the next `outlen` bytes of that output to `out`, and leaves \
    in `*state` a state, and returns a position, that continue it after its first `n + outlen` \
    bytes. Start from the state `vg_{X.rust}_finalize` leaves and position 0.\n\n\
    Contract: `VG.Spec.Sha3.xofSqueezeContract` for `VG.Spec.Sha3.xof{xofName.capitalize}`. \
    Constant time: only the pointers, `pos` and `outlen` may affect timing, not the state."
  safety := [s!"`pos` must be at most {X.rate}."]

def updateShake128Api : Api := updateApi xofShake128.name xofShake128.rust xofShake128.rate
def finalizeShake128Api : Api := xofFinalizeApi xofShake128 "shake128"
def finalizeShake256Api : Api := xofFinalizeApi xofShake256 "shake256" "vg_sha3_256_update"
def squeezeShake128Api : Api := xofSqueezeApi xofShake128 "shake128"
def squeezeShake256Api : Api := xofSqueezeApi xofShake256 "shake256"

/-- The rates in the contracts are the sponges' of FIPS 202 (§6): `(1600 - c) / 8`
for each function's capacity `c` (`keccak`). -/
example : hashSha3_224.rate = (1600 - 448) / 8 ∧ hashSha3_256.rate = (1600 - 512) / 8 ∧
    hashSha3_384.rate = (1600 - 768) / 8 ∧ hashSha3_512.rate = (1600 - 1024) / 8 ∧
    xofShake128.rate = (1600 - 256) / 8 ∧ xofShake256.rate = (1600 - 512) / 8 := by decide

end VG.Spec.Sha3
