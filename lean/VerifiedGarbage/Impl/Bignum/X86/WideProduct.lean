module

public import VerifiedGarbage.Impl.Mont.X86.Dynamic

/-! # Full-width schoolbook multiplication for RSA factor checks and CRT recombination -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86

/-- `ebp = edi + 4*i`; add the ith row without Montgomery reduction. -/
def wideProductRow (N out a b mult : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .ebp a)), .store (sc mult) .eax])
    (.seq (Dynamic.mulRowW out b N mult)
      (.block [.alu .add .ebp (.imm 4), .mov .edx (.reg .edi),
        .alu .add .edx (.imm (BitVec.ofNat 32 (4 * N))), .alu .cmp .ebp (.reg .edx)]))

/-- `N` 32-bit words per operand; `2*N+1` output words, including a zero guard word. -/
def wideProduct (N out a b mult : Nat) : Prog isa :=
  .seq (Dynamic.zerosW out (2 * N + 1))
    (.seq (.block [.mov .ebp (.reg .edi)]) (.loop (wideProductRow N out a b mult) .ne))

end VG.Impl.Bignum.X86
