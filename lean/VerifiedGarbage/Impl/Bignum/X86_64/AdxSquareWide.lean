import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareMac

/-! Longer register-scalar multiply-add chains for Montgomery reduction. -/
namespace VG.Impl.Bignum.X86_64.AdxSquareWide
open VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Adx

/-- Store each low word without changing either carry flag. -/
def word (k : Nat) (hi prev : Reg) : List Instr :=
  wordA k hi .r11 prev ++ [.store (ix .r8 .r14 (8 * k)) .r11]

def pair (k : Nat) : List Instr := word k .rax .rcx ++ word (k + 1) .rcx .rax

/-- An even number of words returns its high half to `rcx`. -/
def chain : Nat → Nat → List Instr
  | 0, _ => []
  | n + 1, k => pair k ++ chain n (k + 2)

def block : List Instr := [.alu32 .xor .rsi (.reg .rsi)] ++ chain 8 0 ++ close .rcx ++
  [.alu .add .r14 (.imm 16), .alu .cmp .r14 (.reg .rbx)]

/-- Multiples of sixteen use the longer chain; other sizes use the
four-word row, including its exact remainder handling. -/
def row : Prog isa :=
  .seq (.block [.mov .rbx (.reg .rbp), .alu .and .rbx (.imm 15), .alu .cmp .rbx (.imm 0)])
    (.ite .e
      (.seq (.block [.mov .rbx (.reg .rbp), .mov32 .rcx (.imm 0), .mov32 .r14 (.imm 0)])
        (.loop (.block block) .ne)) AdxSquare.macRow)
end VG.Impl.Bignum.X86_64.AdxSquareWide
