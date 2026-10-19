module
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Spec.Weierstrass.Point
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Impl.Rsa.X86.Recover

import VerifiedGarbage.Proof.Mont.X86.ExponentTiming

/-! # Initialization blocks use only the public workspace and stack addresses -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Recover

/-- The stack pointer is public in addition to the workspace pointer. -/
def AddressPublic (c : Prog isa) : Prop := ∃ hint out,
  VG.Taint.check taint argumentTaint c hint = some out ∧
  taint.le argumentTaint out = true

theorem AddressPublic.seq {a b : Prog isa} (ha : AddressPublic a) (hb : AddressPublic b) :
    AddressPublic (.seq a b) := by
  obtain ⟨ah, ao, ac, al⟩ := ha
  obtain ⟨bh, bo, bc, bl⟩ := hb
  exact ⟨.seq argumentTaint ah bh, bo, exponent_check_seq taint ac al bc, bl⟩

theorem AddressPublic.trace {c : Prog isa} (h : AddressPublic c) :
    RelCT isa (VG.X86.Taint.Agree argumentTaint) c (fun _ _ => True) := by
  obtain ⟨hint, out, checked, _⟩ := h
  apply VG.RelCT.taint (A := taint) argumentTaint (fun _ _ h => h) (hc := hint)
  rw [checked]
  rfl

theorem candSet_address (n : Nat) : AddressPublic (candSet n) := by
  let reference := Code.erase (candSet 1)
  let hint := VG.Taint.hintOf taint argumentTaint reference
  let out := (VG.Taint.check taint argumentTaint reference hint).getD argumentTaint
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (candSet n) reference argumentTaint hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem halfInit_address (n : Nat) : AddressPublic (halfInit n) := by
  let reference := Code.erase (halfInit 1)
  let hint := VG.Taint.hintOf taint argumentTaint reference
  let out := (VG.Taint.check taint argumentTaint reference hint).getD argumentTaint
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (halfInit n) reference argumentTaint hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem sqInit_address : AddressPublic (.block sqInit) := by
  let reference := Code.erase (.block sqInit)
  let hint := VG.Taint.hintOf taint argumentTaint reference
  let out := (VG.Taint.check taint argumentTaint reference hint).getD argumentTaint
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (.block sqInit) reference argumentTaint hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem eqS_address (n d a b t : Nat) : AddressPublic (VG.Impl.Rsa.X86.Keys.eqS n d a b t) := by
  let reference := Code.erase (VG.Impl.Rsa.X86.Keys.eqS 1 100 0 1 2)
  let hint := VG.Taint.hintOf taint argumentTaint reference
  let out := (VG.Taint.check taint argumentTaint reference hint).getD argumentTaint
  refine ⟨hint, out, ?_, ?_⟩
  · exact (check_of_erase_eq (VG.Impl.Rsa.X86.Keys.eqS n d a b t) reference argumentTaint hint rfl rfl rfl).trans (by rfl)
  · decide +kernel

theorem candSquareInit_address (n : Nat) : AddressPublic
    (VG.Impl.Rsa.X86.Keys.seqs [eqAt n sE1 mY aO, eqAt n sE2 mY aNg, .block sqInit]) :=
  (eqS_address ..).seq ((eqS_address ..).seq sqInit_address)

end VG.Proof.Rsa.X86.Recover
