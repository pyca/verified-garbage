module

public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.Impl.MlKem.RISCV64.Poly

/-!
# ML-KEM on RISC-V: `SampleNTT`

As on PPC64LE (`Impl/MlKem/PPC64LE/Sample.lean`), with the sponge
functions of `Impl/Sha3/RISCV64/Stream.lean`, which run in frames on the
stack and take no working space.

`vg_mlkem_sample_ntt(seed = a0, a = a1, scratch = a2) -> a0`: the 2048
bytes of `scratch` hold the Keccak state (`[0, 200)`), the 840 bytes of XOF
output (`[840, 1680)`), and our caller's `s7`–`s9` and our return address
(`[1680, 1712)`). `s7`, `s8` and `s9` keep `seed`, `a` and `scratch`
across the calls (the callees preserve them). The state is zeroed (the
empty message), the 34 bytes of the seed absorbed with rate 168, the SHAKE
padding (`0x1f`) absorbed, and 840 bytes squeezed: 280 chunks of three
bytes, which the loop of Algorithm 7 then goes through (`rejBody`), with
`a0` the next chunk, `a1` the next coefficient of `a`, `a2` the number `j`
of coefficients accepted, `a3` the chunks left and `q` in `t3`. A candidate
`d` is accepted if `d < q` and `j < 256`: the AND of the sign bits of
`d - q` and `j - 256` is not zero. It returns `j >> 8`: 1 if `j = 256`.

The function has no stack frame of its own; the sponge functions' frames
use the 1168 bytes below the stack pointer.

The loop's branches depend on the XOF output, a function of the seed, which
the contract lets the function leak; every address depends only on the
pointers and on `j`, likewise.
-/

@[expose] public section

namespace VG.Impl.MlKem.RISCV64

open VG.RISCV64
open VG.Impl.Sha3.RISCV64.Stream (mov)

/-- The Keccak state at `[b]` zeroed, through `t0`. -/
def zeroState (b : Reg) : List Instr :=
  [.li .t0 0] ++ (List.range 25).flatMap fun k => [.store .d .t0 b (8 * k)]

/-- Our caller's registers and our return address saved, the arguments
moved to `s7`–`s9`, the state zeroed. -/
def sampleSetup : List Instr :=
  [.store .d .s7 .a2 1680, .store .d .s8 .a2 1688, .store .d .s9 .a2 1696, .store .d .ra .a2 1704,
    mov .s7 .a0, mov .s8 .a1, mov .s9 .a2] ++ zeroState .s9

/-- `absorb(state, 168, 0, seed, 34)`. -/
def absorbSeedArgs : List Instr := [mov .a0 .s9, .li .a1 168, .li .a2 0, mov .a3 .s7, .li .a4 34]

/-- `pad(state, 168, pos, 0x1f)`, with `pos` from `absorb`. -/
def padArgs : List Instr := [mov .a2 .a0, mov .a0 .s9, .li .a1 168, .li .a3 0x1f]

/-- `squeeze(state, 168, 0, scratch + 840, 840)`. -/
def squeezeArgs : List Instr := [mov .a0 .s9, .li .a1 168, .li .a2 0, .addi .a3 .s9 840, .li .a4 840]

/-- `t2 = 0` unless the candidate `d` is accepted: `d < q` (`q` in `t3`) and
`j = a2 < 256`. -/
def acceptTest (d : Reg) : List Instr :=
  [.sub .t2 d .t3, .shift .srl .d .t2 .t2 63, .addi .a4 .a2 (-256), .shift .srl .d .a4 .a4 63,
    .logic .and .t2 .t2 .a4]

/-- The candidate `d` stored as the next coefficient, if accepted. -/
def accept (d : Reg) : Prog isa :=
  .ite (.zero .t2) (.block []) (.block [.store .w d .a1 0, .addi .a1 .a1 4, .addi .a2 .a2 1])

/-- The two candidates of the chunk at `a0`: `d₁` in `a7`, `d₂` in `t1`. -/
def candidates : List Instr :=
  [.load .b .a4 .a0 0, .load .b .a5 .a0 1, .load .b .a6 .a0 2, .shift .sll .d .a7 .a5 60,
    .shift .srl .d .a7 .a7 52, .add .a7 .a4 .a7, .shift .srl .d .t1 .a5 4, .shift .sll .d .t2 .a6 4,
    .add .t1 .t1 .t2]

/-- An iteration of Algorithm 7, lines 5–15. -/
def rejBody : Prog isa :=
  .seq (.block (candidates ++ acceptTest .a7))
  (.seq (accept .a7)
  (.seq (.block (acceptTest .t1))
  (.seq (accept .t1)
    (.block [.addi .a0 .a0 3, .addi .a3 .a3 (-1)]))))

/-- The return value, and our caller's registers and the return address
restored (`s9`, the base, last). -/
def sampleEnd : List Instr :=
  [.shift .srl .d .a0 .a2 8, .load .d .ra .s9 1704, .load .d .s7 .s9 1680, .load .d .s8 .s9 1688,
    .load .d .s9 .s9 1696]

def sampleNTT : Prog isa :=
  .seq (.block sampleSetup)
  (.seq (.seq (.block absorbSeedArgs) (.call Spec.Sha3.absorbApi.name Impl.Sha3.RISCV64.Stream.absorb))
  (.seq (.seq (.block padArgs) (.call Spec.Sha3.padApi.name Impl.Sha3.RISCV64.Stream.pad))
  (.seq (.seq (.block squeezeArgs) (.call Spec.Sha3.squeezeApi.name Impl.Sha3.RISCV64.Stream.squeeze))
  (.seq (.block ([.addi .a0 .s9 840, mov .a1 .s8, .li .a2 0, .li .a3 280] ++ liq .t3 3329))
  (.seq (.loop rejBody (.nonzero .a3)) (.block sampleEnd))))))

end VG.Impl.MlKem.RISCV64
