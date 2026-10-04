import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase
import VerifiedGarbage.Impl.Sha3.Arm.Stream
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Setup
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Entry
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Wipe

/-!
# Ed448 public-key derivation on ARMv7

`vg_ed448_public_key(out = r0, seed = r1, scratch = r2)` computes
`SHAKE256(seed, 114)` with the sponge functions (`vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze`, rate 136), prunes the first 57
bytes of the hash (RFC 8032 §5.2.5) and encodes `[s]B` with
`vg_ed448_scalar_base`.

The frame is Ed25519's on this target (`Impl/Ed25519/Arm/Whole`): 248 bytes
of locals from `sp`, the arguments saved above them, and `r12` and `lr`
pushed. The sponge functions' stack arguments are at `sp`; the hash is
squeezed into the frame at `sp + 24` and pruned there in place, so that the
scalar `vg_ed448_scalar_base` reads lies outside `scratch` and `out`, which
it writes; the frame is cleared before it is popped. In `scratch`: the
Keccak state (200 bytes) and the sponge functions' working space (640 bytes,
at 208). Every address depends only on the pointers and `sp`.
-/

namespace VG.Impl.Ed448.Arm.PublicKey

open VG.Arm
open VG.Impl.Ed25519.Arm.Whole

/-- Where in the frame the hash, and then the scalar, is. -/
def HASH : Nat := 24

/-- Where in `scratch` the sponge functions' working space is. -/
def KSCR : Nat := 208

/-- The Keccak state at `scratch`, zeroed: `scratch` into `r0`, and then the
stores, in a block of their own. -/
def zeroArgs : List Instr := setup [(.r0, .caller 2 0), (.r1, .const 0)] []

def zeroStores : List Instr := (List.range 50).map fun k => .str .r1 .r0 (4 * k)

def zeroState : Prog isa := .seq (.block zeroArgs) (.block zeroStores)

/-- `absorb(state = scratch, rate = 136, pos = 0, data = seed, len = 57,
scratch + 208)`. -/
def absorbArgs : List Instr :=
  setup [(.r0, .caller 2 0), (.r1, .const 136), (.r2, .const 0), (.r3, .caller 1 0)]
    [.const 57, .caller 2 KSCR]

/-- `pad(state = scratch, rate = 136, pos = 57, suffix = 0x1f, scratch + 208)`. -/
def padArgs : List Instr :=
  setup [(.r0, .caller 2 0), (.r1, .const 136), (.r2, .const 57), (.r3, .const 0x1f)]
    [.caller 2 KSCR]

/-- `squeeze(state = scratch, rate = 136, pos = 0, out = sp + 24, len = 114,
scratch + 208)`. -/
def squeezeArgs : List Instr :=
  setup [(.r0, .caller 2 0), (.r1, .const 136), (.r2, .const 0), (.r3, .frame HASH)]
    [.const 114, .caller 2 KSCR]

/-- `SHAKE256(seed, 114)` into the frame at `HASH`. -/
def hash : Prog isa :=
  .seq zeroState <|
  .seq (callWith absorbArgs Spec.Sha3.absorbApi.name Impl.Sha3.Arm.Stream.absorb) <|
  .seq (callWith padArgs Spec.Sha3.padApi.name Impl.Sha3.Arm.Stream.pad)
    (callWith squeezeArgs Spec.Sha3.squeezeApi.name Impl.Sha3.Arm.Stream.squeeze)

/-- Pruning (`Spec.Ed448.prune`), in place on the first 57 bytes of the
hash, from `r12 = sp + 24`: bits 0–1 of byte 0 cleared, bit 7 of byte 55
set, and byte 56 cleared. -/
def pruneOps : List Instr :=
  [.ldrb .r0 .r12 0, .dp .and .r0 .r0 (.imm 0xfc), .strb .r0 .r12 0,
    .ldrb .r0 .r12 55, .dp .orr .r0 .r0 (.imm 0x80), .strb .r0 .r12 55,
    .movw .r0 0, .strb .r0 .r12 56]

def prune : Prog isa := .seq (.block [.addSp .r12 HASH]) (.block pruneOps)

/-- `scalar_base(out, scalar = sp + 24, scratch)`. -/
def baseArgs : List Instr := setup [(.r0, .caller 0 0), (.r1, .frame HASH), (.r2, .caller 2 0)] []

/-- The frame from `HASH` on, cleared. -/
def wipe : List Instr := zeroWords 6 56

def body : Prog isa :=
  .seq hash <| .seq prune <|
  .seq (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase) (.block wipe)

/-- `vg_ed448_public_key`. -/
def code : Prog isa := wrap 3 body

end VG.Impl.Ed448.Arm.PublicKey
