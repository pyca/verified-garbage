module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundArithmeticCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorPower
import VerifiedGarbage.Proof.Dsa.X86.ValidationBlocksTiming
import VerifiedGarbage.Proof.Dsa.X86.WidthConstant
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorPower
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundArithmeticCT
import VerifiedGarbage.Proof.Mont.X86.Exponentiate

/-! # Generator success is determined only by the public exponentiation result -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Ecdsa.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

structure GeneratorPublic where
  base : Addr
  size : Nat
  modulus : Nat
  value : Nat
  exponent : Nat

def GeneratorPublic.result (p : GeneratorPublic) : Nat := p.value ^ p.exponent % p.modulus

structure GeneratorPowerAt (n : Nat) (p : GeneratorPublic) (s : State) : Prop where
  context : Context n p.modulus p.base p.size s
  width : n ≤ 48
  one : wordsVal s.mem p.base (slot n 3) n = 1
  r2 : wordsVal s.mem p.base (slot n 4) n = 2 ^ (128 * n) % p.modulus
  value : wordsVal s.mem p.base (slot n 5) n = p.value
  exponent : val32 s.mem p.base (slot n 8) (2 * n) = p.exponent

def GeneratorPoweredAt (n : Nat) (p : GeneratorPublic) (s : State) : Prop :=
  Context n p.modulus p.base p.size s ∧ wordsVal s.mem p.base (slot n 6) n = p.result

theorem generatorExponentiate_ct (n : Nat) (positive : 0 < n) : RelCT isa (Two (GeneratorPowerAt n))
    (exponentiate n (2 * n)) (Two (GeneratorPoweredAt n)) := by
  refine two_post ((exponentiate_ct n (2 * n)).mono ?_ (fun _ _ h => h)) ?_
  · rintro s t ⟨p, hs, ht⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.context.scr.edi_toNat.trans ht.context.scr.edi_toNat.symm)
  · intro p s R
    refine WP.mono (exponentiate_ok R.context (by omega) (Nat.le_refl _) (by have := R.width; omega) R.one R.r2)
      fun t ⟨C, value, _, _⟩ => ?_
    exact ⟨C, by rw [value, R.value, R.exponent]; rfl⟩

theorem generatorLowerTwo_ct (n : Nat) (positive : 0 < n) : RelCT isa (Two (GeneratorPoweredAt n))
    (VG.Impl.Dsa.X86.lessThanConstant n (slot n 6) (slot n 7) 2)
      (Two fun (p : GeneratorPublic) s => s.gpr .eax = mask32 (p.result < 2)) := by
  refine two_post ((lessThanConstant_relCT n (slot n 6) (slot n 7) 2).mono ?_ (fun _ _ _ => trivial)) ?_
  · rintro s t ⟨p, hs, ht⟩
    apply agree_regs
    intro r hr
    have eq : r = .edi := by simpa [workspaceTaint] using hr
    subst r
    exact BitVec.eq_of_toNat_eq (hs.1.scr.edi_toNat.trans ht.1.scr.edi_toNat.symm)
  · intro p s R
    have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ p.size := by
      have := slot_bound (n := n) hj
      have := R.1.size_le
      unfold stride at *; omega
    refine WP.mono (lessThanConstant_ok R.1.scr positive (bounds 6 (by decide)) (bounds 7 (by decide))
      (by have := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ 64 * n); omega)
      (.inl (by simp only [slot, stride]; omega))) fun t ⟨ax, _, _⟩ => ?_
    rw [ax, R.2]

theorem generatorPower_ct (n : Nat) (positive : 0 < n) :
    RelCT isa (Two (GeneratorPowerAt n)) (generatorPower n) (fun _ _ => True) := by
  refine RelCT.seq (generatorExponentiate_ct n positive) (RelCT.seq (generatorLowerTwo_ct n positive) ?_)
  refine two_taint [.eax] ?_ (by taint_decide)
  intro p s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.trans ht.symm
end VG.Proof.Dsa.X86.Generation
