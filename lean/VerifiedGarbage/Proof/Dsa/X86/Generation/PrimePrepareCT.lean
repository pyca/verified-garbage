module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInputs
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Prime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrepareExponentCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundArithmeticCT
import VerifiedGarbage.Proof.Mont.X86.ContextInit

/-! # A candidate's shared Montgomery context and odd exponent are prepared once -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def PrimeInputsAt (len : Nat) (G : PrimeConfig) (s : State) : Prop := G.len = len ∧ PrimeInputs G s

def PrimeSetupAt (len : Nat) (G : PrimeConfig) (s : State) : Prop :=
  G.len = len ∧ Context G.n G.modulus G.base G.size s ∧
    wordsVal s.mem G.base (slot G.n 3) G.n = 1 ∧ G.modulus % 2 = 1

def primeFactorPublic (G : PrimeConfig) : FactorPublic := ⟨G.base, G.size, G.modulus - 1, 0⟩

theorem primeContextSetup_ct (len : Nat) :
    RelCT isa (Two (PrimeInputsAt len)) (contextSetup ((len + 7) / 8)) (Two (PrimeSetupAt len)) := by
  refine two_post ((contextSetup_ct _).mono ?_ (fun _ _ h => h)) ?_
  · rintro s t ⟨G, hs, ht⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.2.scratch.edi_toNat.trans ht.2.scratch.edi_toNat.symm)
  · rintro G s ⟨hl, R⟩
    rw [← hl]
    have positive : 0 < G.n := by have := G.lenMin; unfold PrimeConfig.n; omega
    have width := G.width
    have room := G.room
    refine WP.mono (contextSetup_ok (n := G.n) R.scratch positive (by omega)
      (by unfold contextBytes slot stride primeExponent at *; omega) R.modulus R.gtOne R.odd)
      fun t ⟨C, one, _, _, _⟩ => ?_
    exact ⟨rfl, C, one, R.odd⟩

theorem primePrepare_ct (len : Nat) (minimum : 4 ≤ len) :
    RelCT isa (Two (PrimeInputsAt len)) (primePrepare len) (fun _ _ => True) := by
  refine RelCT.seq (primeContextSetup_ct len) (two_map primeFactorPublic ?_
    (prepareExponent_ct ((len + 7) / 8) (by omega)))
  rintro G s ⟨hl, C, one, odd⟩
  rw [← hl]
  have gt := C.gt_one
  have eq : G.modulus - 1 + 1 = G.modulus := by omega
  refine ⟨?_, one, ?_, G.width, G.room⟩
  · change Context G.n (G.modulus - 1 + 1) G.base G.size s
    rw [eq]; exact C
  · change (G.modulus - 1) % 2 = 0; omega
end VG.Proof.Dsa.X86.Generation
