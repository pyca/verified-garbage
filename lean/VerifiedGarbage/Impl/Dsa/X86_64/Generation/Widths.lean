module

public import VerifiedGarbage.Impl.ForwardCall.X86_64

/-! # Parameter generation by the public modulus width, on x86-64

`widths` compares `p_len` (`rdx`) with 128 and 256 and calls the function for
that width, `body₁₂₈`, `body₂₅₆` or `body₃₈₄`, with the arguments it was
given (`forward`, in a frame of 56 bytes, which keeps `rsp` 16-byte aligned at
the call).
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation.Widths
open VG VG.X86_64 VG.Impl.ForwardCall.X86_64

/-- The call of the function `name` for one width. -/
def width (name : String) (body : Prog isa) : Prog isa := forward 56 6 name body

/-- The choice among the two larger widths. -/
def large (n₂₅₆ n₃₈₄ : String) (c₂₅₆ c₃₈₄ : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 256)]) (Code.iteCold .e (width n₂₅₆ c₂₅₆) (width n₃₈₄ c₃₈₄))

def widths (n₁₂₈ n₂₅₆ n₃₈₄ : String) (c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 128)]) (Code.iteCold .e (width n₁₂₈ c₁₂₈) (large n₂₅₆ n₃₈₄ c₂₅₆ c₃₈₄))

end VG.Impl.Dsa.X86_64.Generation.Widths
