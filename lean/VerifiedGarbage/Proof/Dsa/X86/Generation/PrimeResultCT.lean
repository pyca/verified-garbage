module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeUniform
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeControl
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeUniform

/-! # Primality status follows the public round result and uniform-witness count -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86
open VG.Impl.Dsa.X86.Generation

structure PrimeResultPublic where
  base : Addr
  size : Nat
  uniform : Nat
  isUniform : Bool
  passed : Bool

def ResultDataAt (p : PrimeResultPublic) (s : State) : Prop :=
  Scr s p.base p.size ∧ primeIsUniform + 4 ≤ p.size ∧ p.uniform + 1 < 2 ^ 32 ∧
    s.mem.readW (off p.base primeIsUniform) 32 = mask32 (p.isUniform = true) ∧
    s.mem.readW (off p.base primeUniform) 32 = BitVec.ofNat 32 p.uniform

def ResultAt (p : PrimeResultPublic) (s : State) : Prop :=
  ResultDataAt p s ∧ s.gpr .eax = BitVec.ofNat 32 p.passed.toNat

theorem uniformDecision_ct (checks : Nat) (bound : checks < 2 ^ 32) :
    RelCT isa (Two ResultDataAt) (.seq (.block (primeUniformUpdate checks))
      (.ite .ae (.block (primeMark 1)) (.block (primeMark 4)))) (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := fun p s => Scr s p.base p.size ∧
      s.cf = some (decide (p.uniform + p.isUniform.toNat < checks))) [.edi] ?_ (hc := .block []) (by rfl) ?_) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.1.edi_toNat.trans ht.1.edi_toNat.symm)
  · intro p s R
    refine WP.mono (primeUniformUpdate_ok R.1 R.2.1 R.2.2.1 bound R.2.2.2.1 R.2.2.2.2)
      fun t ⟨_, cf, _, K⟩ => ?_
    exact ⟨R.1.of_keeps K (by decide), cf⟩
  · apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
    all_goals
      refine two_taint [.edi] ?_ (by taint_decide)
      intro p s t hs ht r hr
      obtain rfl := List.mem_singleton.mp hr
      exact BitVec.eq_of_toNat_eq (hs.1.1.edi_toNat.trans ht.1.1.edi_toNat.symm)

theorem primeRoundResult_ct (checks : Nat) (bound : checks < 2 ^ 32) :
    RelCT isa (Two ResultAt) (primeRoundResult checks) (fun _ _ => True) := by
  unfold primeRoundResult
  refine RelCT.seq (two_piece (Ψ := fun p s => ResultDataAt p s ∧ s.zf = some (Bool.not p.passed))
    [.eax] ?_ (by taint_decide) ?_) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.trans ht.2.symm
  · intro p s R
    refine wp_cmpi fun t st _ zf => WP.block_nil ?_
    refine ⟨⟨R.1.1.of_keeps (st.keeps [.eax, .ecx]) (by decide), R.1.2.1, R.1.2.2.1,
      by rw [st.mem]; exact R.1.2.2.2.1, by rw [st.mem]; exact R.1.2.2.2.2⟩, ?_⟩
    rw [zf, R.2]; cases p.passed <;> decide +kernel
  · apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2])
    · refine two_taint [.edi] ?_ (by taint_decide)
      intro p s t hs ht r hr
      obtain rfl := List.mem_singleton.mp hr
      exact BitVec.eq_of_toNat_eq (hs.1.1.1.edi_toNat.trans ht.1.1.1.edi_toNat.symm)
    · exact (uniformDecision_ct checks bound).mono (fun _ _ => two_mono (fun _ _ h => h.1.1)) (fun _ _ h => h)
end VG.Proof.Dsa.X86.Generation
