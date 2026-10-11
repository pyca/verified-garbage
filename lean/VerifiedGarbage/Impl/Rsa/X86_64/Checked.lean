module

public import VerifiedGarbage.Impl.Rsa.X86_64

/-!
# RSA within BoringSSL's limits on the public exponent, on x86-64

`vg_rsa_public_checked` and `vg_rsa_public_precomputed_checked` take the
arguments of `vg_rsa_public` and `vg_rsa_public_precomputed`, with the
public exponent `e` in `r8` and its length `e_len` (at least 1) in `r9`.
Before anything else, `expCheck` decides whether `e` is odd and from 3 to
`2^33 - 1` (BoringSSL's `rsa_check_public_key`), using only `rax`, `r10`
and `r11`, so that the arguments stay where the function they guard
expects them: zeros to `out` and 0 returned if not (`failOut`), that
function's code if so.

`expCheck` reads the bytes of `e`, most significant first, into `r11`
saturated: `x` while the bytes so far make `x < 2^33`, `2^34 - 1` from the
first that does not (`256 (2^34 - 1) + 255 < 2^64`). There is no branch:
the saturation is masked, so that only the loop's count, `e_len`, and the
addresses `e + i` affect timing; the check's result is the one branch, on
public data.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.Checked

open VG VG.X86_64 VG.Impl.Bignum.X86_64

/-- `[r8 + r10]`: byte `r10` of `e`. -/
def eByte : MemOp := { base := .r8, index := some .r10 }

/-- One byte of `e`: `r11 := 256 r11 + e[r10]`, then `2^34 - 1` if that is
`2^33` or more; `r10 += 1`, and ZF set when it is `e_len`. -/
def expStep : List Instr :=
  [.shift .ror .r11 56, .movzx8 .rax eByte, .alu .add .r11 (.reg .rax),
    .mov .rax (.reg .r11), .shift .shr .rax 33, .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .alu .and .r11 (.reg .rax), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .shift .shr .rax 30,
    .alu .or .r11 (.reg .rax), .alu .add .r10 (.imm 1), .alu .cmp .r10 (.reg .r9)]

/-- ZF set if the saturated `e` in `r11` is below `2^33`, odd and at least
3. -/
def expTest : List Instr :=
  [.mov .rax (.reg .r11), .shift .shr .rax 33, .mov .r10 (.reg .r11), .alu .and .r10 (.imm 1),
    .alu .xor .r10 (.imm 1), .alu .or .rax (.reg .r10), .alu .cmp .r11 (.imm 3), .alu .sbb .r10 (.reg .r10),
    .alu .or .rax (.reg .r10), .alu .test .rax (.reg .rax)]

/-- ZF set if `e` is within BoringSSL's limits. -/
def expCheck : Prog isa :=
  .seq (.block [.mov32 .r11 (.imm 0), .mov32 .r10 (.imm 0)])
    (.seq (.loop (.block expStep) .ne) (.block expTest))

/-- Zeros to the `out_len` (at least 1) bytes of `out`, and 0 returned. -/
def failOut : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .mov .r10 (.reg .rdi), .mov .r11 (.reg .rsi)])
    (.loop (.block [.store8 (at0 .r10) .rax, .alu .add .r10 (.imm 1), .alu .sub .r11 (.imm 1)]) .ne)

/-- `c`, if `e` is within BoringSSL's limits. -/
def guarded (c : Prog isa) : Prog isa := .seq expCheck (.ite .ne failOut c)

/-- `vg_rsa_public_checked`. -/
def publicChecked : Prog isa := guarded Public.code

/-- `vg_rsa_public_precomputed_checked`, with Montgomery multiplication `mul`. -/
def precomputedChecked (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  guarded (Precomputed.code mul)

end VG.Impl.Rsa.X86_64.Checked
