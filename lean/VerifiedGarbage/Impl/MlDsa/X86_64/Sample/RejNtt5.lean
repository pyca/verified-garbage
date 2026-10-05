import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt4

/-!
# ML-DSA matrix sampling with five initial SHAKE128 blocks

Squeeze three blocks and parse them, then two more and parse 112 candidates.
If all four polynomials have 256 coefficients, return without a sixth
permutation. Otherwise squeeze the sixth block and parse its 56 candidates.
The failure bound and sampled coefficients are those of the six-block code.
Counts are saved between batches; checking them is allowed to leak the
public matrix seeds, just like the rejection sampler itself.
-/

namespace VG.Impl.MlDsa.X86_64.Sample.Rej5

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)
open VG.Impl.MlKem.X86_64.Sample4 (pro epi absorb4 squeeze4 oRc oBuf)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ zeroJ first)
open VG.Impl.Sha3.X86_64.X4 (rcTable)

/-- Start a segment at candidate `off` of one 504-byte buffer. -/
def setup (k off count : Nat) : List Instr :=
  [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * k + 3 * off))),
   .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * k))),
   .mov .rdi (.mem (at_ .rbx (oJ + 8 * k))), .mov32 .rcx (.imm (BitVec.ofNat 32 count))]

/-- Parse `count` candidates, starting at `off`. -/
def parse (k off count : Nat) : Prog isa := .seq (.block (setup k off count)) (.loop rnBody .ne)

/-- Parse a segment and save its coefficient count. -/
def segment (k off count : Nat) : Prog isa :=
  .seq (parse k off count) (.block [.store (at_ .rbx (oJ + 8 * k)) .rdi])

/-- Parse a segment of all four buffers. -/
def batch (off count : Nat) : Prog isa :=
  .seq (segment 0 off count) (.seq (segment 1 off count) (.seq (segment 2 off count) (segment 3 off count)))

/-- `r14` is one iff every stored count is 256. Counts never exceed 256. -/
def flags : List Instr := .mov32 .r14 (.imm 1) :: (List.range 4).flatMap fun k =>
  [.mov .rax (.mem (at_ .rbx (oJ + 8 * k))), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)]

/-- The optional sixth block, with the accumulator reset before squeezing. -/
def fallback : Prog isa :=
  .seq (.block [.mov32 .r14 (.imm 1)])
    (.seq (squeeze4 2) (.seq (batch 112 56) (.block flags)))

/-- Check the five-block result and finish with the original six-block bound. -/
def finish : Prog isa :=
  .seq (.block (flags ++ [.alu32 .cmp .r14 (.imm 0)]))
    (.seq (.ite .e fallback (.block [])) (.block ([.vop .vzeroupper] ++ VG.Impl.MlKem.X86_64.Sample4.epi)))

def rejNTT4Avx2 : Prog isa :=
  .seq (.block (VG.Impl.MlKem.X86_64.Sample4.pro ++ rcTable .rbx (oRc / 32) ++ absorb4))
    (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (.block zeroJ)
      (.seq (first 0) (.seq (first 1) (.seq (first 2) (.seq (first 3)
        (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (batch 0 112) finish)))))))))))

end VG.Impl.MlDsa.X86_64.Sample.Rej5
