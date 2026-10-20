module
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Impl.Dsa.X86.Width

/-! # Reuse p's Montgomery constants to evaluate a generator candidate -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

/-- Slot 5 holds h and slot 8 holds (p-1)/q. Slot 6 receives g;
EAX is 1 when g > 1, or 3 when the generator tape must advance. -/
def generatorPower (n : Nat) : Prog isa :=
  .seq (exponentiate n (2 * n))
    (.seq (lessThanConstant n (slot n 6) (slot n 7) 2)
      (.seq (.block [.alu .cmp .eax (.imm 0)])
        (.ite .e (.block [.mov .eax (.imm 1)]) (.block [.mov .eax (.imm 3)]))))
end VG.Impl.Dsa.X86.Generation
