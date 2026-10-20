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

def ArithmeticReady (base : Addr) (size n : Nat) (s : State) : Prop :=
  ∃ modulus, Context n modulus base size s ∧
    wordsVal s.mem base (slot n 3) n = 1 ∧
    wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % modulus

theorem arithmeticHead_ok {base : Addr} {size len bl : Nat} {modulus : Field} {a b : Pointer} {s : State}
    (P : ArithmeticPre base size len bl modulus a b s) (hz : Layout.saved ≤ size)
    (h4 : 4 ≤ len) (hmax : len ≤ 384) (hb4 : 4 ≤ bl) (hb : bl ≤ len) (hw4 : len % 4 = 0)
    (hwb : bl % 4 = 0) :
    WP isa (arithmeticHead len bl modulus a b) s (ArithmeticReady base size ((len + 7) / 8)) := by
  have hn : (len + 7) / 8 ≤ 48 := by omega
  unfold arithmeticHead
  refine WP.seq (WP.mono (coreSetup_ok P.scr hz rfl h4 hmax hw4 P.modulusReady.toReadableComponent
    (P.modulusReady.slot (by decide)) rfl P.large P.odd) fun u ⟨C, One, R2, O, K⟩ => ?_)
  refine WP.mono (coreInputs_ok C hz hn h4 (by omega) hb4 (by omega) hw4 hwb
    (P.leftReady.keep K (by decide) O hn) (P.rightReady.keep K (by decide) O hn))
    fun t ⟨Ct, _, _, Constants, _, _⟩ => ?_
  exact ⟨_, Ct, (Constants 3 (.inl rfl)).trans One, (Constants 4 (.inr rfl)).trans R2⟩

end VG.Proof.Dsa.X86
