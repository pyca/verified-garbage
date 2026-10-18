module

public import VerifiedGarbage.Proof.Dsa.X86.SigningOperation

/-! # Whole-operation functional correctness against the shared DSA contracts -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem verifyingSharedPost {s t : State}
    (V : (t.gpr .eax).toNat = (if Spec.Dsa.verifyBytes (arg s 2).toNat (arg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat) then 1 else 0)) :
    (Spec.Dsa.verifyContract abi 32).post s t := by
  sig_post [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argSlots, argVal, argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _
  rw [BitVec.setWidth_append_eq_right]
  exact V

theorem signingSharedPost {s t : State}
    (V : (t.gpr .eax).toNat = Spec.Dsa.signStatus (Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)))
    (B : Spec.Rsa.bytesAt t.mem (argumentPointer s 0) (arg s 1).toNat =
      (Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)).getD
          (List.replicate (arg s 1).toNat 0)) :
    (Spec.Dsa.signContract abi 32).post s t := by
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes]
  change ((t.gpr .edx ++ t.gpr .eax).setWidth 32).toNat = _ ∧ _
  rw [BitVec.setWidth_append_eq_right]
  exact ⟨V, B⟩

theorem verifyingCorrect (s : State) (h : (Spec.Dsa.verifyContract abi 32).pre s) :
    ∃ trace t, Exec isa (Entry.operation false) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.verifyContract abi 32).post s t := by
  obtain ⟨trace, t, E, V, ABI, _⟩ := verifyingOperation_spec (verifyingABI_of h)
  exact ⟨trace, t, E, ABI, verifyingSharedPost V⟩

theorem signingCorrect (s : State) (h : (Spec.Dsa.signContract abi 32).pre s) :
    ∃ trace t, Exec isa (Entry.operation true) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.signContract abi 32).post s t := by
  obtain ⟨trace, t, E, V, B, ABI, _⟩ := signingOperation_spec (signingABI_of h)
  exact ⟨trace, t, E, ABI, signingSharedPost V B⟩

end VG.Proof.Dsa.X86
