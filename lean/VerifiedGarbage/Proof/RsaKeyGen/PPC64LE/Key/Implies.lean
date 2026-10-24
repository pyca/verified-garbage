module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Contract
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_keygen_key` on PPC64LE: the shared contract implies `keyP`

As `vg_rsa_crt_values`'s (`Proof/Rsa/PPC64LE/CvImplies.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG VG.PPC64LE

/-- A state meeting `keyP.pre`: 32-byte primes, a one-byte exponent, the
outputs at `0x1000`–`0x1600`, `e` at `0x1700`, the working space at
`0x8000`, and the stack arguments at `sp + 96 = 0x6060`. -/
def keySatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x1100 | .r6 => 64 | .r7 => 0x1200 | .r8 => 32 | .r9 => 0x1300
    | .r10 => 32 | _ => 0
  lr := 0
  sp := 0x6000
  mem a := if a = 0x6061 then 0x14 else if a = 0x6068 then 0x20 else if a = 0x6071 then 0x15
    else if a = 0x6078 then 0x20 else if a = 0x6081 then 0x16 else if a = 0x6088 then 0x20
    else if a = 0x6091 then 0x17 else if a = 0x6098 then 1 else if a = 0x60A1 then 0x80
    else if a = 0x60A8 then 0x20 else if a = 0x60A9 then 0x04 else 0
  rd := [⟨0x1700, 1⟩, ⟨0x6060, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x1200, 32⟩, ⟨0x1300, 32⟩, ⟨0x1400, 32⟩, ⟨0x1500, 32⟩, ⟨0x1600, 32⟩,
    ⟨0x8000, 8448⟩]

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

theorem key_implies : keyP.Implies (Spec.RsaKeyGen.keyContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyP, stackArgs_ten,
      List.append_eq] at h
    sig_pre [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyP, stackArgs_ten,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyP, stackArgs_ten,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | omega
  post := by
    sig_implies_post [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyP, stackArgs_ten,
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyP, stackArgs_ten,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, -, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_ten, stackArgs_ten, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyP, stackArgs_ten,
      List.append_eq] [keySatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.RsaKeyGen.primeLenValid,
        Spec.Rsa.scratchWords] using keySatState

end VG.Proof.RsaKeyGen.PPC64LE.Key
