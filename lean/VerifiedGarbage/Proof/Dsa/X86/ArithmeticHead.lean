module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame

import VerifiedGarbage.Proof.Dsa.X86.CoreInputs
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup

/-! # Common context and operand preparation for powers, products, and sums -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def arithmeticHead (len bl : Nat) (modulus : Field) (a b : Pointer) : Prog isa :=
  .seq (Core.setup len modulus)
    (.seq (Core.load ((len + 7) / 8) len (slot ((len + 7) / 8) 5) a)
      (Core.load ((len + 7) / 8) bl (slot ((len + 7) / 8) 8) b))

structure ArithmeticPre (base : Addr) (size len bl : Nat) (modulus : Field) (a b : Pointer) (s : State) : Prop where
  scr : Scr s base size
  modulusReady : OperandReady s base ((len + 7) / 8) (.input modulus) len
  leftReady : OperandReady s base ((len + 7) / 8) a len
  rightReady : OperandReady s base ((len + 7) / 8) b bl
  large : 1 < Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len)
  odd : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) % 2 = 1

end VG.Proof.Dsa.X86
