module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Refill
public import VerifiedGarbage.Impl.ForwardCall.X86_64

/-! # `vg_dsa_parameter_search_init` and `vg_dsa_parameter_search` on x86-64

The search chooses its width's function by `state[1]`, the modulus's width,
and forwards its arguments to it (as `Generation.Widths` does for
`vg_dsa_generate_parameters`). `init` writes the four public words of
`Spec.Dsa.parameterInit`. -/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.ParameterSearch

open VG VG.X86_64 VG.Impl.ForwardCall.X86_64

/-- The call of `name` for one width, with the two stack arguments. -/
def width (name : String) (body : Prog isa) : Prog isa := forward 56 2 name body

/-- `state[1]` into `rax`, compared with `n`. -/
def widthOf (n : Nat) : List Instr :=
  [.mov .rax (.mem { base := .rsp, disp := 16 }), .mov .rax (.mem { base := .rax, disp := 8 }),
   .alu .cmp .rax (.imm (BitVec.ofNat 32 n))]

def widths (n₁₂₈ n₂₅₆ n₃₈₄ : String) (c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa) : Prog isa :=
  .seq (.block (widthOf 128)) (Code.iteCold .e (width n₁₂₈ c₁₂₈)
    (.seq (.block [.alu .cmp .rax (.imm 256)]) (Code.iteCold .e (width n₂₅₆ c₂₅₆) (width n₃₈₄ c₃₈₄))))

/-- `vg_dsa_parameter_search_init(state, p_len)`: `[4096, p_len, 32769 *
p_len, 512 * p_len]` and 1 for a supported width, else zeros and 0. -/
def initWords : List Instr :=
  [.mov32 .rax (.imm 4096), .store { base := .rdi, disp := 0 } .rax, .store { base := .rdi, disp := 8 } .rsi,
   .mov .rax (.reg .rsi), .shift .shl .rax 15, .alu .add .rax (.reg .rsi),
   .store { base := .rdi, disp := 16 } .rax,
   .mov .rax (.reg .rsi), .shift .shl .rax 9, .store { base := .rdi, disp := 24 } .rax,
   .mov32 .rax (.imm 1)]

def initZeros : List Instr :=
  [.mov32 .rax (.imm 0), .store { base := .rdi, disp := 0 } .rax, .store { base := .rdi, disp := 8 } .rax,
   .store { base := .rdi, disp := 16 } .rax, .store { base := .rdi, disp := 24 } .rax]

def init : Prog isa :=
  .seq (.block [.alu .cmp .rsi (.imm 128)])
    (.ite .e (.block initWords)
      (.seq (.block [.alu .cmp .rsi (.imm 256)])
        (.ite .e (.block initWords)
          (.seq (.block [.alu .cmp .rsi (.imm 384)])
            (.ite .e (.block initWords) (.block initZeros))))))

end VG.Impl.Dsa.X86_64.ParameterSearch
