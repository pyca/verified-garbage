module

public import VerifiedGarbage.Impl.SlhDsa.X86_64.Thash4

/-!
# SLH-DSA on x86-64: four SHAKE256 hashes, one after the other

The baseline implementation of `thash4` (`Impl/SlhDsa/X86_64/Thash4.lean`),
for CPUs without AVX2: `thash4With` with the states zeroed by scalar stores
and permuted one at a time (`permute4S`): each copied from its interleaved
lanes to `work[800..1000)`, permuted there by the scalar Keccak-f[1600]
(`vg_keccak_f1600`, with its 512 bytes of working space at
`work[1000..1512)`), and copied back. The calls keep only the callee-saved
registers, so `r9`–`r11` (the lanes' addresses) are kept in `xmm8`–`xmm10`
across them, with the three values in `work[2368..2392)` in `xmm11`–`xmm13`
(`park`, `unpark`), and `r8` (`work`) is recovered from `rdi`, the state's
address, which the permutation returns unchanged. As `permute4`, it keeps
`r8`–`r11`. It uses only SSE2's `movq`s of the vector instructions.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.X86_64.Thash4Base

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)

/-- Where the state being permuted and the permutation's working space are,
in `work`. -/
def oSt : Nat := 800
def oKs : Nat := 1000

/-- The states zeroed with scalar stores. -/
def zeroS : List Instr := .mov32 .rax (.imm 0) :: (List.range 100).map fun i => .store (at_ .r8 (8 * i)) .rax

/-- State `k` from its interleaved lanes to `work[800..1000)`, through `rax`. -/
def gather (k : Nat) : List Instr :=
  (List.range 25).flatMap fun i => [.mov .rax (.mem (at_ .r8 (32 * i + 8 * k))), .store (at_ .r8 (oSt + 8 * i)) .rax]

/-- And back. -/
def scatter (k : Nat) : List Instr :=
  (List.range 25).flatMap fun i => [.mov .rax (.mem (at_ .r8 (oSt + 8 * i))), .store (at_ .r8 (32 * i + 8 * k)) .rax]

/-- State `k` permuted: gathered, `vg_keccak_f1600` on it, and scattered. -/
def permOne (k : Nat) : Prog isa :=
  .seq (.block (gather k ++ [.mov .rdi (.reg .r8), .alu .add .rdi (.imm (BitVec.ofNat 32 oSt)), .mov .rsi (.reg .r8),
      .alu .add .rsi (.imm (BitVec.ofNat 32 oKs))]))
    (.seq (.call "vg_keccak_f1600" Impl.Sha3.X86_64.permute)
      (.block ([.mov .r8 (.reg .rdi), .alu .sub .r8 (.imm (BitVec.ofNat 32 oSt))] ++ scatter k)))

/-- `r9`–`r11` and the three values `permuteKeep` keeps in `work[2368..2392)`,
to `xmm8`–`xmm13`. -/
def park : List Instr :=
  [.xop (.movq .xmm8 .r9), .xop (.movq .xmm9 .r10), .xop (.movq .xmm10 .r11),
    .mov .rax (.mem (at_ .r8 Thash4.oPtr)), .xop (.movq .xmm11 .rax),
    .mov .rax (.mem (at_ .r8 Thash4.oLeft)), .xop (.movq .xmm12 .rax),
    .mov .rax (.mem (at_ .r8 Thash4.oPos)), .xop (.movq .xmm13 .rax)]

/-- And back, the three values stored again to their slots. -/
def unpark : List Instr :=
  [.movqR .r9 .xmm8, .movqR .r10 .xmm9, .movqR .r11 .xmm10,
    .movqR .rax .xmm11, .store (at_ .r8 Thash4.oPtr) .rax,
    .movqR .rax .xmm12, .store (at_ .r8 Thash4.oLeft) .rax,
    .movqR .rax .xmm13, .store (at_ .r8 Thash4.oPos) .rax]

/-- The four states at `r8` permuted. The calls keep neither `r9`–`r11`
nor, for the constant-time analysis, anything it knows of memory (a call's
return address is stored where the analysis cannot place it), so those and
the values in `work[2368..2392)` are kept in `xmm8`–`xmm13`, which the
scalar permutation does not write, and the values are stored again
after the calls. -/
def permute4S : Prog isa :=
  .seq (.block park)
    (.seq (permOne 0) (.seq (permOne 1) (.seq (permOne 2) (.seq (permOne 3) (.block unpark)))))

/-- The baseline `thash4` for outputs of `n` bytes. -/
def thash4 (n : Nat) : Prog isa := Thash4.thash4With zeroS permute4S n []

end VG.Impl.SlhDsa.X86_64.Thash4Base
