module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Refill
public import VerifiedGarbage.Impl.ForwardCall.X86_64

/-! # `vg_dsa_parameter_search_init` and `vg_dsa_parameter_search` on x86-64

The search chooses its width's function by `state[1]`, the modulus's width,
and forwards its arguments to it (as `Generation.Widths` does for
`vg_dsa_generate_parameters`), with the addresses of the functions the
search calls indirectly in `rax`, `r10` and `r11`: one search for a width
serves every implementation of the hash and of the prime test. `init` writes the four public words of
`Spec.Dsa.parameterInit`. -/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.ParameterSearch

open VG VG.X86_64 VG.Impl.ForwardCall.X86_64

/-- `rax`, `r10` and `r11` to the addresses of the functions `u`, `f` and
`p`: those the search for a width calls indirectly, its hash's `update` and
`finalize` and its prime test (`Generation.viaSlot`). -/
def fnAddrs (u f p : String) : List Instr := [.leaSym .rax u, .leaSym .r10 f, .leaSym .r11 p]

/-- The call of `name` for one width, with the two stack arguments copied
(`forward`) and then the addresses `fns` in their registers. -/
def width (fns : List Instr) (name : String) (body : Prog isa) : Prog isa :=
  .frame (.alloc 56) (.seq (.block (copies 56 2 ++ fns)) (.call name body)) (.free 56)

/-- `state[1]` into `rax`, compared with `n`. -/
def widthOf (n : Nat) : List Instr :=
  [.mov .rax (.mem { base := .rsp, disp := 16 }), .mov .rax (.mem { base := .rax, disp := 8 }),
   .alu .cmp .rax (.imm (BitVec.ofNat 32 n))]

def widths (f₁₂₈ f₂₅₆ f₃₈₄ : List Instr) (n₁₂₈ n₂₅₆ n₃₈₄ : String) (c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa) :
    Prog isa :=
  .seq (.block (widthOf 128)) (Code.iteCold .e (width f₁₂₈ n₁₂₈ c₁₂₈)
    (.seq (.block [.alu .cmp .rax (.imm 256)]) (Code.iteCold .e (width f₂₅₆ n₂₅₆ c₂₅₆) (width f₃₈₄ n₃₈₄ c₃₈₄))))

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
