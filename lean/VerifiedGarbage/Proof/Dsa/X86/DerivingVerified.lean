module

public import VerifiedGarbage.Proof.Dsa.X86.DerivingLayout
import VerifiedGarbage.Proof.Dsa.X86.DerivingOperation
import VerifiedGarbage.Proof.Dsa.X86.DerivingOperationCT

/-! # The i686 key derivation meets its shared contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem derivingPublicArgs {s t : State} (H : (Spec.Dsa.deriveKeyContract abi 108).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 9, arg s i = arg t i := by
  sig_pub [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem derivingPublicParams {s t : State} (H : (Spec.Dsa.deriveKeyContract abi 108).pub s t) :
    derivingParams s = derivingParams t := by
  have Args := (derivingPublicArgs H).2
  have Bytes : (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat).map (·.toNat) := by
    sig_pub [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argSlots, argVal, argBytes] at H
    exact List.append_inj_left' H.2.1 rfl
  have Eq := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 Bytes
  simp only [derivingParams, Args 4 (by decide), Args 6 (by decide), Eq]

theorem derivingCorrect (s : State) (h : (Spec.Dsa.deriveKeyContract abi 108).pre s) :
    ∃ trace t, Exec isa Generate.deriveKey s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.deriveKeyContract abi 108).post s t := by
  obtain ⟨trace, t, E, V, B, ABI, _⟩ := derivingOperation_spec (derivingABI_of h)
  refine ⟨trace, t, E, ABI, ?_⟩
  sig_post [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argSlots, argVal, argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _ ∧ _
  rw [BitVec.setWidth_append_eq_right]
  exact ⟨V, B⟩

theorem derivingConstantTime : ConstantTime isa (Spec.Dsa.deriveKeyContract abi 108).pre
    (Spec.Dsa.deriveKeyContract abi 108).pub Generate.deriveKey := by
  intro s t tr ur sf tf S T H E F
  have Args := derivingPublicArgs H
  have Params := derivingPublicParams H
  exact derivingOperation_agrees (derivingABI_of S) (derivingABI_of T) Args.2 Args.1
    (congrArg Spec.Dsa.Params.p Params) (congrArg Spec.Dsa.Params.q Params) E F

/-- A disjoint supported-width call whose zero domain is rejected. -/
def derivingSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 168 else if a = 0x20009 then 1 else if a = 0x2000d then 32 else if a = 0x20010 then 20 else if a = 0x20011 then 1 else if a = 0x20014 then 128 else if a = 0x20019 then 48 else if a = 0x2001c then 20 else if a = 0x20021 then 128 else if a = 0x20025 then 8 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x3000, 20⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x8000, 16384⟩, ⟨0x20004, 36⟩]

theorem derivingSatisfiable : ∃ s, (Spec.Dsa.deriveKeyContract abi 108).pre s := by
  have a0 : arg derivingSatState 0 = 4096 := by decide
  have a1 : arg derivingSatState 1 = 424 := by decide
  have a2 : arg derivingSatState 2 = 8192 := by decide
  have a3 : arg derivingSatState 3 = 276 := by decide
  have a4 : arg derivingSatState 4 = 128 := by decide
  have a5 : arg derivingSatState 5 = 12288 := by decide
  have a6 : arg derivingSatState 6 = 20 := by decide
  have a7 : arg derivingSatState 7 = 32768 := by decide
  have a8 : arg derivingSatState 8 = 2048 := by decide
  have e : argAddr derivingSatState 0 = 0x20004 := by decide
  have esp : derivingSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig,
    abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, e, esp, derivingSatState] using derivingSatState

theorem deriving_verified :
    Verified target Generate.deriveKey (Spec.Dsa.deriveKeyContract abi 108) :=
  ⟨derivingCorrect, derivingConstantTime, derivingSatisfiable⟩

end VG.Proof.Dsa.X86
