module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorCT
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundMinus
import VerifiedGarbage.Proof.Dsa.X86.Generation.Factor
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrepareExponent
import VerifiedGarbage.Proof.Dsa.X86.Generation.CopyCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundArithmeticCT

/-! # Preparing the public odd exponent and saving it once per candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def PrepareAt (n : Nat) (p : FactorPublic) (s : State) : Prop :=
  Context n (p.value + 1) p.base p.size s ∧ wordsVal s.mem p.base (slot n 3) n = 1 ∧
    p.value % 2 = 0 ∧ n ≤ 48 ∧ primeExponent + 8 * n ≤ p.size

def PrepareFactorAt (n : Nat) (p : FactorPublic) (s : State) : Prop :=
  FactorEntryAt n p s ∧ n ≤ 48 ∧ primeTwos + 4 ≤ p.size

theorem prepareMinus_ct (n : Nat) :
    RelCT isa (Two (PrepareAt n)) (roundMinusOne n) (Two (PrepareFactorAt n)) := by
  refine two_post ((roundMinusOne_ct n).mono ?_ (fun _ _ h => h)) ?_
  · rintro s t ⟨p, hs, ht⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.1.scr.edi_toNat.trans ht.1.scr.edi_toNat.symm)
  · intro p s R
    refine WP.mono (roundMinusOne_ok R.1 R.2.1) fun t ⟨C, value, _, _⟩ => ?_
    have width := R.2.2.2.1
    have room := R.2.2.2.2
    refine ⟨⟨C.scr, by have := C.gt_one; omega, R.2.2.1, ?_, ?_⟩, width, ?_⟩
    · simp only [slot, stride, primeExponent] at *; omega
    · rw [← wordsVal_eq_val32, value, Nat.add_sub_cancel]
    · unfold primeTwos primeExponent at *; omega

theorem prepareFactor_ct (n : Nat) (positive : 0 < n) :
    RelCT isa (Two (PrepareFactorAt n)) (factor n) (Two FactorScratchAt) := by
  refine two_post ((factor_ct n positive).mono (fun _ _ => two_mono (fun _ _ h => h.1)) (fun _ _ h => h)) ?_
  intro p s R
  refine WP.mono (factor_ok R.1.1 positive R.2.1 R.1.2.2.2.1 R.2.2 R.1.2.1 R.1.2.2.1 R.1.2.2.2.2)
    fun t ⟨_, _, _, K⟩ => ?_
  exact R.1.1.of_keeps K (by decide)

theorem prepareExponent_ct (n : Nat) (positive : 0 < n) :
    RelCT isa (Two (PrepareAt n)) (prepareExponent n) (fun _ _ => True) := by
  refine RelCT.seq (prepareMinus_ct n) (RelCT.seq (prepareFactor_ct n positive) ?_)
  refine (copyWords_ct _ _ _).mono ?_ (fun _ _ h => h)
  rintro s t ⟨p, hs, ht⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (hs.edi_toNat.trans ht.edi_toNat.symm)
end VG.Proof.Dsa.X86.Generation
