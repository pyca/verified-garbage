module

public import VerifiedGarbage.Impl.Sha3.AArch64.Stream
public import VerifiedGarbage.Impl.MlKem.AArch64.Basic
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt

/-!
# ML-KEM on AArch64: an iteration of `SampleNTT`'s loop

One iteration of the loop of Algorithm 7 on a chunk of three bytes of
SHAKE128 output (`sampleBody`), which the samplers of `Rej8.lean` run on the
chunks their vector steps leave: the chunk's two candidates (`sampleChunk`),
each stored as the next coefficient and counted only if it is less than `q`
(`sampleAccept`), and nothing once there are 256 coefficients.

It keeps `x2` = the next chunk of output, `x3` = the next coefficient,
`x4` = the coefficients still to accept, `x5` = the iterations left,
`x9` = `q` and `x10` = 15. Its branches and the addresses it writes depend
on the output, and so on the seed, which the contract declares that the
function may leak.
-/

@[expose] public section

namespace VG.Impl.MlKem.AArch64

open VG.AArch64

/-- Accept the candidate `d` if it is less than `q`, without a branch: store
it as the next coefficient either way, and count it (`x14`) only if it is
accepted, so that a rejected one is overwritten by the next. With `w16` the
coefficients are 16 bits apart: the store's upper half writes zero to the next
coefficient, or to the two bytes past the last. -/
def sampleAccept (d : Reg) (w16 : Bool := false) : List Instr :=
  [.sub .x .x13 d .x9, .lsr .x .x14 .x13 63, .str .w d .x3 0, .lsl .x .x15 .x14 (if w16 then 1 else 2),
    .add .x .x3 .x3 .x15, .sub .x .x4 .x4 .x14]

/-- The candidates `d₁` (`x11`) and `d₂` (`x12`) of the chunk at `x2`. -/
def sampleChunk : List Instr :=
  [.ldrb .x6 .x2 0, .ldrb .x7 .x2 1, .ldrb .x8 .x2 2, .addImm .x .x2 .x2 3, .subImm .x .x5 .x5 1,
    .logic .and .x .x11 .x7 .x10, .lsl .x .x11 .x11 8, .add .x .x11 .x11 .x6, .lsr .x .x12 .x7 4,
    .lsl .x .x13 .x8 4, .add .x .x12 .x12 .x13]

/-- One iteration: nothing once there are 256 coefficients. -/
def sampleBody (w16 : Bool := false) : Prog isa :=
  .seq (.block sampleChunk)
    (.ite (.zero .x .x4) (.block [])
      (.seq (.block (sampleAccept .x11 w16)) (.ite (.zero .x .x4) (.block [])
        (.block (sampleAccept .x12 w16)))))

end VG.Impl.MlKem.AArch64
