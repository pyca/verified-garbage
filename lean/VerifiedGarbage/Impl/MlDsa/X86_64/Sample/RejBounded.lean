module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Common

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_bounded_poly`

`rejBoundedShort(seed = rdi, eta = esi, a = rdx, scratch = rcx) -> eax` (see
`Common.lean` for the layout) squeezes 272 bytes of SHAKE256 of the 66 bytes
of the seed (2 blocks), which the first 272 iterations of `RejBoundedPoly`'s
loop take a byte at a time; if fewer than 256 coefficients were accepted, it
squeezes 272 more bytes of the same stream, to 544 (4 blocks; the least
bound of FIPS 204 Appendix C is 481 bytes, the contract's largest 1088), and
resumes the loop for the other 272 (`rbContinue`). Each `η` has its own
code (`rbShort η`, chosen by a branch on the public `η`). The loop has `rsi`
at the byte of the iteration, `rdi` = `j`, the number of coefficients sampled,
and `rcx` counting down: while `j < 256`, each half-byte `b` of the byte (low
first, in `rdx`) that `CoeffFromHalfByte` accepts (`b < 15` for `η = 2`,
`b < 9` for `η = 4`) gives the coefficient `η - (b mod 5)` or `η - b`,
stored modulo `q` to `a[j]` (and `j` incremented; the high half-byte only if
`j < 256` still). It returns `j >> 8`: 1 if `j = 256`, and 0 otherwise.

The coefficient is computed without a branch or a table (`rbVal`): `b mod 5`
by subtracting 10 and then 5 where they are no greater, `sub` setting CF when
they are greater and `sbb` making it a mask, and `q` added under a mask to
`η - (b mod 5)` if it is negative. So the loop's branches and the addresses
of its stores depend only on which half-bytes are accepted (and `j`, which
counts them), which the contract lets it leak, not on the coefficients.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.Sample

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)

/-- `rdx ← rdx - s` if `s ≤ rdx`, with `r8` as a mask. -/
def csub (s : BitVec 32) : List Instr :=
  [.alu32 .sub .rdx (.imm s), .alu32 .sbb .r8 (.reg .r8), .alu32 .and .r8 (.imm s), .alu32 .add .rdx (.reg .r8)]

/-- `r8 ← (η - rdx) mod q`, for `rdx ≤ q + η`, with `rdx` as a mask. -/
def etaSub (η : BitVec 32) : List Instr :=
  [.mov32 .r8 (.imm η), .alu32 .sub .r8 (.reg .rdx), .alu32 .sbb .rdx (.reg .rdx), .alu32 .and .rdx (.imm qImm),
    .alu32 .add .r8 (.reg .rdx)]

/-- The coefficient of an accepted half-byte `rdx`, modulo `q`, in `r8`:
`η - (b mod 5)` for `η = 2`, `η - b` for `η = 4`. -/
def rbVal : Nat → List Instr
  | 2 => csub 10 ++ csub 5 ++ etaSub 2
  | _ => etaSub 4

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbBound : Nat → BitVec 32
  | 2 => 15
  | _ => 9

/-- Store the coefficient of the half-byte `rdx` to `a[j]` if it is accepted. -/
def rbTry (η : Nat) : Prog isa :=
  .seq (.block [.alu32 .cmp .rdx (.imm (rbBound η))])
    (.ite .b (.block (rbVal η ++ ([.store32 aJ .r8, .alu .add .rdi (.imm 1)] : List Instr))) (.block []))

/-- The byte at `rsi` in `rax`, its low half-byte in `rdx`, and `j < 256` in CF. -/
def rbLoad : List Instr :=
  [.movzx8 .rax (at_ .rsi 0), .mov32 .rdx (.reg .rax), .alu32 .and .rdx (.imm 15), .alu .cmp .rdi (.imm 256)]

/-- The high half-byte in `rdx`, and `j < 256` in CF. -/
def rbHi : List Instr := [.shift32 .shr .rax 4, .mov32 .rdx (.reg .rax), .alu .cmp .rdi (.imm 256)]

def rbBody (η : Nat) : Prog isa :=
  .seq (.block rbLoad)
    (.seq (.ite .b (.seq (rbTry η) (.seq (.block rbHi) (.ite .b (rbTry η) (.block [])))) (.block []))
      (.block [.alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]))

/-- The loop, from the XOF output at `scratch + 840`. -/
def rbLoopCount (η count : Nat) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)])
    (.seq (.block [.mov32 .rcx (.imm (BitVec.ofNat 32 count))]) (.loop (rbBody η) .ne))

/-- Save the ordinary sampler layout. -/
def rbShortPro : List Instr :=
  [.store (at_ .rcx 2024) .rbx, .store (at_ .rcx 2032) .rbp, .store (at_ .rcx 2040) .r12,
    .mov .rbx (.reg .rcx), .mov .rbp (.reg .rdx), .mov .rcx (.reg .rdi), .mov32 .r8 (.imm 66)]

/-- Append the remaining SHAKE bytes and resume at the accepted coefficient
count, using the same parser and the existing four-block bound. -/
def rbContinueArgs (η : Nat) : Prog isa :=
  .seq (.block saveCount) (.seq (squeezeMore 136 1112 272) (.block (resumeArgs 1112 272 ++ [.mov32 .r12 (.imm (BitVec.ofNat 32 η))])))

def rbContinue (η : Nat) : Prog isa :=
  .seq (rbContinueArgs η) (.seq (.loop (rbBody η) .ne) (.block (retJ ++ epi)))

/-- Sample two blocks first; if needed, continue the same SHAKE stream and
coefficient list to the original four-block bound. -/
def rbShort (η : Nat) : Prog isa :=
  .seq (.block rbShortPro) (.seq (spongeStream 136 272) (.seq (rbLoopCount η 272)
    (.seq (.block [.alu .cmp .rdi (.imm 256)])
      (.ite .e (.block (retJ ++ epi)) (rbContinue η)))))

def rejBoundedShort : Prog isa :=
  .seq (.block [.alu32 .cmp .rsi (.imm 2)]) (.ite .e (rbShort 2) (rbShort 4))

end VG.Impl.MlDsa.X86_64.Sample
