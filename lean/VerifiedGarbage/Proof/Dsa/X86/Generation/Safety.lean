module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedAddStructure
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHashes
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialTable

/-! # No parameter-generation instruction writes the stack pointer outside a frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

def generationSafe (c : Prog isa) : Prop := c.all (fun i => !isa.writesSp i) = true

theorem noSp_safe {c : Prog isa} (h : NoSp c) : generationSafe c := by
  apply Code.all_of_allInstrs
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  have eq : (!isa.writesSp i) = !Taint.clobbers i .esp := by cases i <;> rfl
  rw [eq, h i hi]
  rfl

theorem trialTable_safe (n : Nat) : generationSafe (trialTable n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((trialTable n).all _ && (.block (trialTableEntry n) : Prog isa).all _) = true
    rw [ih]
    rfl

theorem seedHash_safe {H : Hash} (K : HashOK H) (len : Nat) : generationSafe (seedHash H len) := by
  have hi := noSp_safe K.initSp
  have hu := noSp_safe K.updSp
  have hf := noSp_safe K.finSp
  simp only [generationSafe, seedHash, Hash.callInit, Code.all] at *
  rw [hi, hu, hf]
  rfl
theorem pHashPrefix_safe {H : Hash} (K : HashOK H) (len count n : Nat) : generationSafe (pHashPrefix H len count n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have seed := seedHash_safe K len
    have add := noSp_safe (seedAdd_noClobber len .esp (by decide) (by decide))
    unfold generationSafe at *
    simp only [pHashPrefix, pHashOne, pSeedHash, Code.all, ih, add, seed]
    rfl

end VG.Proof.Dsa.X86.Generation
