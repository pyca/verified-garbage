module

public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream

/-!
# ML-KEM on PPC64LE: `SampleNTT`

As on 32-bit ARM (`Impl/MlKem/Arm/Sample.lean`), with the sponge's
arguments all in registers.

`vg_mlkem_sample_ntt(seed = r3, a = r4, scratch = r5) -> r3`: the 2048
bytes of `scratch` hold the Keccak state (`[0, 200)`), the working space of
the sponge functions (`[200, 840)`), the 840 bytes of XOF output
(`[840, 1680)`), and our caller's `r29`–`r31` and our return address
(`[1680, 1712)`). `r29`, `r30` and `r31` keep `seed`, `a` and `scratch`
across the calls (the callees preserve them). The state is zeroed (the
empty message), the 34 bytes of the seed absorbed with rate 168, the SHAKE
padding (`0x1f`) absorbed, and 840 bytes squeezed: 280 chunks of three
bytes, which the loop of Algorithm 7 then goes through (`rejBody`), with
`r3` the next chunk, `r4` the next coefficient of `a`, `r5` the number `j`
of coefficients accepted and `r6` the chunks left. A candidate `d` is
accepted if `d < q` and `j < 256`: the AND of the sign bits of `d - q` and
`j - 256` is not zero. It returns `j >> 8`: 1 if `j = 256`.

The function has no stack frame of its own; the sponge functions' frames
use the 48 bytes below the stack pointer.

The loop's branches depend on the XOF output, a function of the seed, which
the contract lets the function leak; every address depends only on the
pointers and on `j`, likewise.
-/

@[expose] public section

namespace VG.Impl.MlKem.PPC64LE

open VG.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)

/-- The Keccak state at `[b]` zeroed, through `r0`. -/
def zeroState (b : Reg) : List Instr :=
  [.li .r0 0] ++ (List.range 25).flatMap fun k => [.store .d .r0 b (8 * k)]

/-- Our caller's registers and our return address saved, the arguments
moved to `r29`–`r31`, the state zeroed. -/
def sampleSetup : List Instr :=
  [.mflr .r0, .store .d .r29 .r5 1680, .store .d .r30 .r5 1688, .store .d .r31 .r5 1696,
    .store .d .r0 .r5 1704, mov .r29 .r3, mov .r30 .r4, mov .r31 .r5] ++ zeroState .r31

/-- `absorb(state, 168, 0, seed, 34, scratch + 200)`. -/
def absorbSeedArgs : List Instr :=
  [mov .r3 .r31, .li .r4 168, .li .r5 0, mov .r6 .r29, .li .r7 34, .addi .r8 .r31 200]

/-- `pad(state, 168, pos, 0x1f, scratch + 200)`, with `pos` from `absorb`. -/
def padArgs : List Instr :=
  [mov .r5 .r3, mov .r3 .r31, .li .r4 168, .li .r6 0x1f, .addi .r7 .r31 200]

/-- `squeeze(state, 168, 0, scratch + 840, 840, scratch + 200)`. -/
def squeezeArgs : List Instr :=
  [mov .r3 .r31, .li .r4 168, .li .r5 0, .addi .r6 .r31 840, .li .r7 840, .addi .r8 .r31 200]

/-- `r12 = 0` unless the candidate `d` is accepted: `d < q` and `j = r5 < 256`. -/
def acceptTest (d : Reg) : List Instr :=
  [.subi .r12 d 3329, .lsr .d .r12 .r12 63, .subi .r7 .r5 256, .lsr .d .r7 .r7 63,
    .logic .and .r12 .r12 .r7]

/-- The candidate `d` stored as the next coefficient, if accepted. -/
def accept (d : Reg) : Prog isa :=
  .ite (.zero .d .r12) (.block []) (.block [.store .w d .r4 0, .addi .r4 .r4 4, .addi .r5 .r5 1])

/-- The two candidates of the chunk at `r3`: `d₁` in `r10`, `d₂` in `r11`. -/
def candidates : List Instr :=
  [.lbz .r7 .r3 0, .lbz .r8 .r3 1, .lbz .r9 .r3 2, .lsl .r10 .r8 60, .lsr .d .r10 .r10 52,
    .add .r10 .r7 .r10, .lsr .d .r11 .r8 4, .lsl .r12 .r9 4, .add .r11 .r11 .r12]

/-- An iteration of Algorithm 7, lines 5–15. -/
def rejBody : Prog isa :=
  .seq (.block (candidates ++ acceptTest .r10))
  (.seq (accept .r10)
  (.seq (.block (acceptTest .r11))
  (.seq (accept .r11)
    (.block [.addi .r3 .r3 3, .subi .r6 .r6 1]))))

/-- The return value, and our caller's registers and the return address
restored (`r31`, the base, last). -/
def sampleEnd : List Instr :=
  [.lsr .d .r3 .r5 8, .load .d .r0 .r31 1704, .mtlr .r0, .load .d .r29 .r31 1680,
    .load .d .r30 .r31 1688, .load .d .r31 .r31 1696]

def sampleNTT : Prog isa :=
  .seq (.block sampleSetup)
  (.seq (.seq (.block absorbSeedArgs) (.call "vg_keccak_absorb_scratch" Impl.Sha3.PPC64LE.Stream.absorb))
  (.seq (.seq (.block padArgs) (.call "vg_keccak_pad_scratch" Impl.Sha3.PPC64LE.Stream.pad))
  (.seq (.seq (.block squeezeArgs) (.call "vg_keccak_squeeze_scratch" Impl.Sha3.PPC64LE.Stream.squeeze))
  (.seq (.block [.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 280])
  (.seq (.loop rejBody (.nonzero .d .r6)) (.block sampleEnd))))))

end VG.Impl.MlKem.PPC64LE
