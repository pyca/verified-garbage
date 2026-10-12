module

public import VerifiedGarbage.Impl.Ed25519.X86.Whole.Setup
public import VerifiedGarbage.Impl.Ed25519.X86.Whole.Wipe
public import VerifiedGarbage.Impl.Sha3.X86.Stream
public import VerifiedGarbage.Spec.Sha3.Contract

/-!
# Ed448 on x86 (32-bit): SHAKE256 of `dom4(0, C) ‖ …` in Ed25519's frame

The blocks with which a complete Ed448 operation in Ed25519's frame on this
target (`Impl/Ed25519/X86/PublicKey.lean`: 64 words pushed, the outgoing
cdecl arguments at `esp`, the caller's arguments at `esp + 260`) hashes,
with the sponge functions (`vg_keccak_absorb_scratch`, `vg_keccak_pad_scratch`,
`vg_keccak_squeeze_scratch`, rate 136, SHAKE's suffix): the Keccak state at
`scratch` and their working space at `scratch + 208`, `scratch` the
caller's argument `sc` (`.caller sc`).

* `hdrAt j off`: the first ten bytes of `dom4(0, context)`
  (`"SigEd448" ‖ 0 ‖ ctxlen`) in the frame at `off`, from the caller's
  argument `j`, `ctxlen` (below 256): the word `ctxlen · 2^8` (the bytes
  `0 ‖ ctxlen`, by eight doublings) at `off + 8`, then `"SigEd448"` in the
  two words before it.
* `zeroState sc`: the Keccak state zeroed, through `eax`.
* `firstArgs`, `nextArgs`: an absorption's arguments, from position 0, or
  from the position the previous one returned in `eax` (kept in `edx`
  while the others are set, and stored last); `padArgs` likewise;
  `sqzArgs`: 114 bytes squeezed into the frame.

Every address depends only on `esp` and `scratch`.
-/

@[expose] public section

namespace VG.Impl.Ed448.X86.Shake

open VG.X86
open VG.Impl.Ed25519.X86.Whole (Value setup at_)

/-- Where in `scratch` the sponge functions' working space is. -/
def KSCR : Nat := 208

def hdrAt (j off : Nat) : List Instr :=
  [.mov .eax (.mem (at_ (260 + 4 * j)))] ++ List.replicate 8 (.alu .add .eax (.reg .eax)) ++
    [.store (at_ (off + 8)) .eax, .mov .eax (.imm 0x45676953), .store (at_ off) .eax,
      .mov .eax (.imm 0x38343464), .store (at_ (off + 4)) .eax]

/-- `scratch` into `eax`, `0` into `edx`. -/
def zeroArgs (sc : Nat) : List Instr := [.mov .eax (.mem (at_ (260 + 4 * sc))), .mov .edx (.imm 0)]

def zeroStores : List Instr := (List.range 50).map fun k => .store ⟨.eax, 4 * k⟩ .edx

/-- The Keccak state at `scratch`, zeroed. -/
def zeroState (sc : Nat) : Prog isa := .block (zeroArgs sc ++ zeroStores)

/-- `absorb(state = scratch, rate = 136, pos = 0, data = src, len, scratch + 208)`. -/
def firstArgs (sc : Nat) (src len : Value) : List Instr :=
  setup 0 [.caller sc 0, .const 136, .const 0, src, len, .caller sc KSCR]

/-- `absorb(state = scratch, rate = 136, pos = eax, data = src, len,
scratch + 208)`: at the position the previous absorption returned. -/
def nextArgs (sc : Nat) (src len : Value) : List Instr :=
  .mov .edx (.reg .eax) :: setup 0 [.caller sc 0, .const 136, .const 0, src, len, .caller sc KSCR] ++
    [.store (at_ 8) .edx]

/-- `pad(state = scratch, rate = 136, pos = eax, suffix = 0x1f, scratch + 208)`. -/
def padArgs (sc : Nat) : List Instr :=
  .mov .edx (.reg .eax) :: setup 0 [.caller sc 0, .const 136, .const 0, .const 0x1f, .caller sc KSCR] ++
    [.store (at_ 8) .edx]

/-- `squeeze(state = scratch, rate = 136, pos = 0, out = esp + d, len = 114,
scratch + 208)`. -/
def sqzArgs (sc d : Nat) : List Instr :=
  setup 0 [.caller sc 0, .const 136, .const 0, .frame d, .const 114, .caller sc KSCR]

def callWith (args : List Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block args) (.call name code)

def absorb (args : List Instr) : Prog isa :=
  callWith args Spec.Sha3.absorbScratchApi.name Impl.Sha3.X86.Stream.absorb

def pad (sc : Nat) : Prog isa :=
  callWith (padArgs sc) Spec.Sha3.padScratchApi.name Impl.Sha3.X86.Stream.pad

def squeeze (sc d : Nat) : Prog isa :=
  callWith (sqzArgs sc d) Spec.Sha3.squeezeScratchApi.name Impl.Sha3.X86.Stream.squeeze

/-- Pruning (`Spec.Ed448.prune`), in place on 57 bytes of the frame at `q`:
bits 0–1 of byte 0 cleared, bit 7 of byte 55 set, and byte 56 cleared. -/
def pruneAt (q : Nat) : List Instr :=
  [.movzx8 .eax (at_ q), .alu .and .eax (.imm 0xfc), .store8 (at_ q) .al,
    .movzx8 .eax (at_ (q + 55)), .alu .or .eax (.imm 0x80), .store8 (at_ (q + 55)) .al,
    .mov .eax (.imm 0), .store8 (at_ (q + 56)) .al]

end VG.Impl.Ed448.X86.Shake
