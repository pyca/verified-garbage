module

public import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
public import VerifiedGarbage.Impl.Sha3.AArch64.Stream
public import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Entry
public import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Setup
public import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Wipe
public import VerifiedGarbage.Impl.Ed448.AArch64.Whole

/-!
# Ed448 public-key derivation on AArch64

`publicKeyWith c (out = x0, seed = x1, scratch = x2)` computes
`SHAKE256(seed, 114)` with the sponge functions (`vg_keccak_absorb_scratch`,
`vg_keccak_pad_scratch` and `vg_keccak_squeeze_scratch`, rate 136, with the
permutation `c`),
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

@[expose] public section

namespace VG.Impl.Ed448.AArch64.PublicKey

open VG.AArch64
open VG.Impl.Ed25519.AArch64.Whole (setup callWith zeroWords wrap)
open VG.Impl.Ed448.AArch64.Whole (zeroStores)

/-- Where the hash is, in the frame, and the sponge functions' working space, in `scratch`. -/
def hashAt : Nat := 128
def keccakScratch : Nat := 256

/-- `x15 = scratch`. -/
def zeroArgs : List Instr := setup [(.x15, .caller 2 0)]

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
  .seq (callWith absorbArgs ("vg_keccak_absorb_scratch" ++ c.suffix)
    (Impl.Sha3.AArch64.Stream.absorbWith c)) <|
  .seq (callWith padArgs ("vg_keccak_pad_scratch" ++ c.suffix) (Impl.Sha3.AArch64.Stream.padWith c))
    (callWith squeezeArgs ("vg_keccak_squeeze_scratch" ++ c.suffix)
      (Impl.Sha3.AArch64.Stream.squeezeWith c))

/-- Pruning (`Spec.Ed448.prune`): the hash, pruned, as the scalar at the bottom of the frame. -/
def prune : List Instr := Impl.Ed448.AArch64.Whole.pruneAt hashAt 0

/-- The scalar and the hash in the frame, cleared. -/
def wipe : List Instr := zeroWords 0 32

def body (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (hash c) <| .seq (.block prune) <|
    .seq (callWith baseArgs "vg_ed448_scalar_base" scalarBase) (.block wipe)

/-- `vg_ed448_public_key`, with the permutation `c`. -/
def publicKeyWith (c : Impl.Sha3.AArch64.Callee) : Prog isa := wrap (body c)

end VG.Impl.Ed448.AArch64.PublicKey
