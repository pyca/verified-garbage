module

public import VerifiedGarbage.Impl.Sha3.X86.Stream

/-!
# SHA-3 and SHAKE on x86 (32-bit): the functions of each instance

Each instance's functions call the sponge's (`Stream`), whose arguments,
like theirs, are on the stack (cdecl), with the rate (and suffix) as
constants. Each allocates a frame (`.alloc`) with the callee's arguments at
its base, `esp`, and, but for `update`, the callee's working space (640
bytes) above them; stores the arguments there (`copy`, a word of the
caller's arguments, at `esp + bytes + 4` and above; `const`; `buf`, an
address in the frame), and calls the sponge function.

* `update rate (state, pos, data, len, scratch)` calls `absorb(state, rate,
  pos, data, len, scratch)` and returns what it returns.
* `xofFinalize rate (state, pos)` calls `pad(state, rate, pos, 0x1f,
  scratch)` (SHAKE's suffix).
* `xofSqueeze rate (state, pos, out, outlen)` calls `squeeze(state, rate,
  pos, out, outlen, scratch)` and returns what it returns.
* `finalize rate len (state, pos, out)` (SHA-3) calls `pad(state, rate,
  pos, 0x06, scratch)` (SHA-3's suffix), then `squeeze(state, rate, 0, out,
  len, scratch)`, setting all of `squeeze`'s arguments again (a callee owns
  its arguments, and may change them).

No register but `eax` is written outside the calls, which preserve the
callee-saved ones, and every address is `esp` and an offset.
-/

@[expose] public section

namespace VG.Impl.Sha3.X86.Instances

open VG.X86

def at_ (d : Nat) : MemOp := ⟨.esp, d⟩

/-- Argument `j` of the caller, in a frame of `bytes` bytes, as argument `k`. -/
def copy (bytes j k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ (bytes + 4 + 4 * j))), .store (at_ (4 * k)) .eax]

/-- `n` as argument `k`. -/
def const (n k : Nat) : List Instr := [.mov .eax (.imm (BitVec.ofNat 32 n)), .store (at_ (4 * k)) .eax]

/-- `esp + d`, an address in the frame, as argument `k`. -/
def buf (d k : Nat) : List Instr :=
  [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 d)), .store (at_ (4 * k)) .eax]

/-- `absorb(state, rate, pos, data, len, scratch)`, from `update`'s arguments. -/
def updateArgs (rate : Nat) : List Instr :=
  copy 24 0 0 ++ const rate 1 ++ copy 24 1 2 ++ copy 24 2 3 ++ copy 24 3 4 ++ copy 24 4 5

def update (rate : Nat) : Prog isa :=
  .frame (.alloc 24)
    (.seq (.block (updateArgs rate)) (.call "vg_keccak_absorb_scratch" Stream.absorb)) (.free 24)

/-- `pad(state, rate, pos, 0x1f, scratch = esp + 20)`, from SHAKE's
`finalize`'s arguments. -/
def xofPadArgs (rate : Nat) : List Instr :=
  copy 660 0 0 ++ const rate 1 ++ copy 660 1 2 ++ const 0x1f 3 ++ buf 20 4

def xofFinalize (rate : Nat) : Prog isa :=
  .frame (.alloc 660)
    (.seq (.block (xofPadArgs rate)) (.call "vg_keccak_pad_scratch" Stream.pad)) (.free 660)

/-- `squeeze(state, rate, pos, out, outlen, scratch = esp + 24)`, from
SHAKE's `squeeze`'s arguments. -/
def xofSqueezeArgs (rate : Nat) : List Instr :=
  copy 664 0 0 ++ const rate 1 ++ copy 664 1 2 ++ copy 664 2 3 ++ copy 664 3 4 ++ buf 24 5

def xofSqueeze (rate : Nat) : Prog isa :=
  .frame (.alloc 664)
    (.seq (.block (xofSqueezeArgs rate)) (.call "vg_keccak_squeeze_scratch" Stream.squeeze))
    (.free 664)

/-- `pad(state, rate, pos, 0x06, scratch = esp + 24)`, from SHA-3's
`finalize`'s arguments. -/
def finPadArgs (rate : Nat) : List Instr :=
  copy 664 0 0 ++ const rate 1 ++ copy 664 1 2 ++ const 0x06 3 ++ buf 24 4

/-- `squeeze(state, rate, 0, out, len, scratch = esp + 24)`. -/
def finSqzArgs (rate len : Nat) : List Instr :=
  copy 664 0 0 ++ const rate 1 ++ const 0 2 ++ copy 664 2 3 ++ const len 4 ++ buf 24 5

def finalize (rate len : Nat) : Prog isa :=
  .frame (.alloc 664)
    (.seq (.block (finPadArgs rate)) <|
     .seq (.call "vg_keccak_pad_scratch" Stream.pad) <|
     .seq (.block (finSqzArgs rate len)) (.call "vg_keccak_squeeze_scratch" Stream.squeeze))
    (.free 664)

end VG.Impl.Sha3.X86.Instances
