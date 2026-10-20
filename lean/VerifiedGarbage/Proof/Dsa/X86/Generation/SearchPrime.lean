module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckPrime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryPrime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryPrimeInputs
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryStack
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryTrial
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchWrites

/-! # Primality testing preserves the complete search context and advances only its witness cursor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem searchPrime_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State}
    {len m used offset : Nat} (R : SearchContext P W s)
    (candidate : W 22 = P.geometry.pointer offset)
    (lo : 4 ≤ len) (hi : len ≤ 384) (words : len % 4 = 0)
    (bits : Spec.RsaKeyGen.bitLength m = 8 * len) (odd : m % 2 = 1)
    (room : offset + len ≤ usedBytes P.geometry.pLen) (before : offset + len ≤ arithmetic)
    (value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off P.geometry.base offset) len) = m)
    (usedValue : W 16 = BitVec.ofNat 32 used) (usedBound : used ≤ P.witnesses.bytes.length) :
    let C := P.geometry.prime P.witnesses len m lo hi words bits odd
    WP isa (checkPrime len) s fun t =>
      let result := primeDecision C s.mem used
      SearchContext P (frameUpdate (frameUpdate W 16 (BitVec.ofNat 32 result.used))
        19 (BitVec.ofNat 32 result.status)) t ∧
      (result.status = 1 → PrimeReady C t) ∧
      Frame (checkPrimeWrites C P.geometry.frameBase ((P.geometry.frame - 16).setWidth 64)) s.mem t.mem ∧
      Keeps trialRegs s t := by
  dsimp only
  have parent : W 5 = P.geometry.parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
  have tape : W 13 = P.witnesses.pointer := (R.fixed 13 (by decide) (by decide)).trans P.witnessPointer
  have tapeLen : W 15 = BitVec.ofNat 32 P.witnesses.bytes.length :=
    (R.fixed 15 (by decide) (by decide)).trans P.witnessLength
  have inputs := generationPrimeInputs R.arena R.representation parent candidate lo hi words bits odd room before value
    tape tapeLen usedValue usedBound (by intro i hi; exact R.witnesses.read i 1 (by omega))
  have trial := generationTrialInputs R.arena (by omega : 2 ≤ len) (by omega : len % 2 = 0)
    (by omega : len < 2 ^ 32) (entries := if len ≤ 128 then 512 else 1024)
    (by split <;> decide) (by split <;> decide) room R.table
  rw [← candidate, ← parent] at trial
  have large : 8161 < m := by
    have bounds := (VG.Proof.Dsa.bitLength_iff_bounds (by omega : 0 < 8 * len)).mp bits
    have power := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 13 ≤ 8 * len - 1)
    have eight : (2 : Nat) ^ 13 = 8192 := by decide
    rw [eight] at power
    omega
  refine WP.mono (checkPrime_ok inputs trial (by rw [R.arena.frameReg]; have := P.geometry.stackSize; omega)
    P.geometry.trial_frame_apart (P.witnesses.below (by decide : 16 ≤ 128)) large) fun t ⟨_, rep, ready, O, K⟩ => ?_
  refine ⟨R.frame rep ?_ (O.sub (checkPrime_parameterWrites _ _ _ _ _ _ _ _ _)) K (by decide), ready, O, K⟩
  intro i _ hx
  have i16 : i ≠ 16 := by intro h; subst i; exact hx (by decide)
  have i19 : i ≠ 19 := by intro h; subst i; exact hx (by decide)
  simp only [frameUpdate, ite_eq_right i19, ite_eq_right i16]
end VG.Proof.Dsa.X86.Generation
