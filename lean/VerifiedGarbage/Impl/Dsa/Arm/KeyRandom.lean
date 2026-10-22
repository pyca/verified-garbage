module

public import VerifiedGarbage.Impl.Dsa.Arm.Random

/-!
# Bounded DSA scalar sampling for key generation on 32-bit ARM

The randomized signer's sampler (`Random.lean`), in the frame of
`vg_dsa_generate_key`, whose random tape is its stack arguments 3 and 4
rather than the signer's 5 and 6. The frame's slots, the scan of q and the
comparison are the signer's: p_len and q_len are the same stack arguments
in both, and q follows p in the packed domain as in the packed key.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.KeyRandom
open VG VG.Arm VG.Impl.Dsa.Arm.Random

/-- Stack arguments: `params_len`, `p_len`, `q_len`, `rand`, `rand_len`,
`scratch`, `scratch_len` (`out`, `out_len`, `used` and `params` are the
registers, saved at `oOut`–`oKey`). -/
def aParamsLen : Nat := 0
def aPLen : Nat := 1
def aQLen : Nat := 2
def aRand : Nat := 3
def aRandLen : Nat := 4
def aScratch : Nat := 5
def aScratchLen : Nat := 6

/-- The draw's source, its count, and its place right-aligned in the
`q_len`-byte scalar. -/
def copyHeader : List Instr :=
  [ld .r1 (arg aRand), ld .r0 oUsed, .dp .add .r1 .r1 (.reg .r0), ld .r2 oWidth,
    .dp .add .r4 .r11 (.imm (BitVec.ofNat 32 oNonce)), ld .r0 (arg aQLen), .dp .add .r4 .r4 (.reg .r0),
    .dp .sub .r4 .r4 (.reg .r2)]

def copyInit : List Instr := copyHeader ++ copyFirst

/-- One masked draw into the scalar. -/
def copy : Prog isa := .seq (.block copyInit) copyRest

/-- Whether the tape has a complete draw left: `Z` iff it is short. -/
def drawHead : List Instr :=
  [ld .r0 (arg aRandLen), ld .r7 oUsed, .dp .sub .r0 .r0 (.reg .r7), ld .r7 oWidth,
    .subs .r0 .r0 (.reg .r7), .mov .r0 (.imm 0), .adc .r0 .r0 (.imm 0), .cmp .r0 (.imm 0)]

/-- One complete draw, or a short tape. Status 4 means keep sampling. -/
def draw : Prog isa :=
  .seq (.block drawHead)
    (.ite .eq (.block [.mov .r0 (.imm 2), st .r0 oStatus])
      (.seq copy
        (.seq (.block [ld .r0 oUsed, ld .r7 oWidth, .dp .add .r0 .r0 (.reg .r7), st .r0 oUsed])
          (.seq inRange drawFinish))))

/-- One budget of 128 draws. -/
def sample : Prog isa :=
  .seq (.block [.mov .r0 (.imm 128), st .r0 oDraws, .mov .r0 (.imm 4), st .r0 oStatus])
    (.seq (.loop (.seq draw (.block [ld .r0 oStatus, .cmp .r0 (.imm 4)])) .eq)
      (.block [ld .r0 oStatus]))

end VG.Impl.Dsa.Arm.KeyRandom
