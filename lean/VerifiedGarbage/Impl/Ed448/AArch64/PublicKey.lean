import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
import VerifiedGarbage.Impl.Sha3.AArch64.Stream
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Entry
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Wipe

/-!
# Ed448 public-key derivation on AArch64

`publicKeyWith c (out = x0, seed = x1, scratch = x2)` computes
`SHAKE256(seed, 114)` with the sponge functions (`vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze`, rate 136, with the permutation `c`),
prunes the first 57 bytes of the hash (RFC 8032 §5.2.5) and encodes `[s]B`
with `vg_ed448_scalar_base`.

It runs in the frame of the complete AArch64 Ed25519 operations
(`Impl.Ed25519.AArch64.Whole.wrap`): `x30` pushed, 320 bytes allocated, the
arguments saved in their last 48 bytes, and each call's arguments set from
them (`setup`). In the first 256 bytes: the pruned scalar (eight words, the
last 0) at 0, which must lie outside `scratch` and `out`, which
`vg_ed448_scalar_base` writes, and the hash (114 bytes) at 128; both are
cleared before the frame is freed. In `scratch`: the Keccak state (200
bytes) and the sponge functions' working space (640 bytes, at 256).
-/

namespace VG.Impl.Ed448.AArch64.PublicKey

open VG.AArch64
open VG.Impl.Ed25519.AArch64.Whole (setup callWith zeroWord zeroWords wrap)

/-- Where the hash is, in the frame, and the sponge functions' working space, in `scratch`. -/
def hashAt : Nat := 128
def keccakScratch : Nat := 256

/-- `x15 = scratch`. -/
def zeroArgs : List Instr := setup [(.x15, .caller 2 0)]

/-- `x14 = 0`, and the 25 words of the Keccak state at `x15` zeroed (in a block of their own:
their address is a pointer read from the frame). -/
def zeroStores : List Instr := .movz .x .x14 0 0 :: (List.range 25).map fun k => .str .x .x14 .x15 (8 * k)

/-- `absorb(state = scratch, rate = 136, pos = 0, data = seed, len = 57, scratch + 256)`. -/
def absorbArgs : List Instr := setup
  [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 0), (.x3, .caller 1 0), (.x4, .const 57),
    (.x5, .caller 2 keccakScratch)]

/-- `pad(state = scratch, rate = 136, pos = 57, suffix = 0x1f, scratch + 256)`. -/
def padArgs : List Instr := setup
  [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 57), (.x3, .const 0x1f),
    (.x4, .caller 2 keccakScratch)]

/-- `squeeze(state = scratch, rate = 136, pos = 0, out = the hash, len = 114, scratch + 256)`. -/
def squeezeArgs : List Instr := setup
  [(.x0, .caller 2 0), (.x1, .const 136), (.x2, .const 0), (.x3, .frame hashAt), (.x4, .const 114),
    (.x5, .caller 2 keccakScratch)]

/-- `scalar_base(out, scalar = the frame, scratch)`. -/
def baseArgs : List Instr := setup [(.x0, .caller 0 0), (.x1, .frame 0), (.x2, .caller 2 0)]

/-- `SHAKE256(seed, 114)` into the frame, with the permutation `c`. -/
def hash (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block zeroArgs) <| .seq (.block zeroStores) <|
  .seq (callWith absorbArgs ("vg_keccak_absorb" ++ c.suffix) (Impl.Sha3.AArch64.Stream.absorbWith c)) <|
  .seq (callWith padArgs ("vg_keccak_pad" ++ c.suffix) (Impl.Sha3.AArch64.Stream.padWith c))
    (callWith squeezeArgs ("vg_keccak_squeeze" ++ c.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith c))

/-- Bits 0–1 of `x9` cleared. -/
def pruneLow : List Instr :=
  [.movz .x .x10 0xfffc 0, .movk .x .x10 0xffff 1, .movk .x .x10 0xffff 2,
    .movk .x .x10 0xffff 3, .logic .and .x .x9 .x9 .x10]

/-- Bit 63 of `x9` set. -/
def pruneHigh : List Instr := [.movz .x .x10 0x8000 3, .logic .orr .x .x9 .x9 .x10]

/-- Word `k` of the hash, pruned, to word `k` of the scalar. -/
def pruneWord (k : Nat) : List Instr :=
  [.ldrSp .x9 (hashAt + 8 * k)] ++
    (if k = 0 then pruneLow else if k = 6 then pruneHigh else []) ++
    [.addSp .x15 (8 * k), .str .x .x9 .x15 0]

/-- Pruning (`Spec.Ed448.prune`): the first seven words of the hash, bits 0–1
cleared and bit 447 (the top of word 6) set, and an eighth word 0, whose low
byte is the 57th. -/
def prune : List Instr :=
  (List.range 7).flatMap pruneWord ++ zeroWord 7

/-- The scalar and the hash in the frame, cleared. -/
def wipe : List Instr := zeroWords 0 32

def body (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (hash c) <| .seq (.block prune) <|
    .seq (callWith baseArgs "vg_ed448_scalar_base" scalarBase) (.block wipe)

/-- `vg_ed448_public_key`, with the permutation `c`. -/
def publicKeyWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := wrap (body c)

end VG.Impl.Ed448.AArch64.PublicKey
