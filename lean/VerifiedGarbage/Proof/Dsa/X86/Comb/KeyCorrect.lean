module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.CheckInvoke
public import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveInvoke
import VerifiedGarbage.Proof.Dsa.X86.Comb.GenerationStack
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Correct

/-! Full functional and ABI correctness of retained-table DSA key generation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

theorem key_correct (s : State) (h : (Spec.Dsa.generateKeyContract abi 156).pre s) :
    ∃ trace t, Exec isa generateKey s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.generateKeyContract abi 156).post s t :=
  KeyRandom.generateKeyWith_correct checkInvoke deriveInvoke keyInvariant_stable
    check_invoke_noSp derive_invoke_noSp s h

end VG.Proof.Dsa.X86.Comb
