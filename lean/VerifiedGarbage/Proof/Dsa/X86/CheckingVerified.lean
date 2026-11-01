module

import VerifiedGarbage.Proof.Dsa.X86.CheckingOperation
import VerifiedGarbage.Proof.Dsa.X86.CheckingOperationCT
public import VerifiedGarbage.Proof.Dsa.X86.CheckingLayout
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # The i686 domain checker meets the shared generation contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem checkingPublicArgs {s t : State} (H : (Proof.Dsa.checkParametersContract abi 108).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 6, arg s i = arg t i := by
  sig_pub [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem checkingPublicParams {s t : State} (H : (Proof.Dsa.checkParametersContract abi 108).pub s t) :
    checkingParams s = checkingParams t := by
  have Args := (checkingPublicArgs H).2
  have Bytes : (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 0) (arg t 1).toNat).map (·.toNat) := by
    sig_pub [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes] at H
    exact H.2.1
  have Eq := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 Bytes
  simp only [checkingParams, Args 2 (by decide), Args 3 (by decide), Eq]

theorem checkingCorrect (s : State) (h : (Proof.Dsa.checkParametersContract abi 108).pre s) :
    ∃ trace t, Exec isa Generate.checkParameters s trace t ∧ abiPreserved s t ∧
      (Proof.Dsa.checkParametersContract abi 108).post s t := by
  obtain ⟨trace, t, E, V, ABI, _⟩ := checkingOperation_spec (checkingABI_of h)
  refine ⟨trace, t, E, ABI, ?_⟩
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _
  rw [BitVec.setWidth_append_eq_right]
  exact V

theorem checkingConstantTime : ConstantTime isa (Proof.Dsa.checkParametersContract abi 108).pre
    (Proof.Dsa.checkParametersContract abi 108).pub Generate.checkParameters := by
  intro s t tr ur sf tf S T H E F
  have Args := checkingPublicArgs H
  have Params := checkingPublicParams H
  exact checkingOperation_agrees (checkingABI_of S) (checkingABI_of T) Args.2 Args.1
    (congrArg Spec.Dsa.Params.p Params) (congrArg Spec.Dsa.Params.q Params) E F

/-- A supported-width, disjoint call; the zero domain is rejected. -/
def checkingSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 32 else if a = 0x20008 then 20 else if a = 0x20009 then 1
    else if a = 0x2000c then 128 else if a = 0x20010 then 20 else if a = 0x20015 then 128
    else if a = 0x20019 then 8 else 0
  rd := [⟨0x2000, 276⟩]
  wr := [⟨0x8000, 16384⟩, ⟨0x20004, 24⟩]

theorem checkingSatisfiable : ∃ s, (Proof.Dsa.checkParametersContract abi 108).pre s := by
  have a0 : arg checkingSatState 0 = 0x2000 := by decide
  have a1 : arg checkingSatState 1 = 276 := by decide
  have a2 : arg checkingSatState 2 = 128 := by decide
  have a3 : arg checkingSatState 3 = 20 := by decide
  have a4 : arg checkingSatState 4 = 0x8000 := by decide
  have a5 : arg checkingSatState 5 = 2048 := by decide
  have e : argAddr checkingSatState 0 = 0x20004 := by decide
  have esp : checkingSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig,
    abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, e, esp, checkingSatState] using checkingSatState

theorem checking_verified :
    Verified target Generate.checkParameters (Proof.Dsa.checkParametersContract abi 108) :=
  ⟨checkingCorrect, checkingConstantTime, checkingSatisfiable⟩

end VG.Proof.Dsa.X86
