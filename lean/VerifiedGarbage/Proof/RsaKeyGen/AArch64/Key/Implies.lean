import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# An RSA key from its primes on AArch64: the shared contract implies `keyA`
-/

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

/-- A state meeting the precondition: 32-byte primes, a one-byte `e`, the
stack arguments at `0x9000`. -/
def keySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 32 | .x6 => 0x4000
    | .x7 => 32 | _ => 0
  sp := 0x9000
  mem a := if a = 0x9001 then 0x50 else if a = 0x9008 then 0x20 else if a = 0x9011 then 0x60 else
    if a = 0x9018 then 0x20 else if a = 0x9021 then 0x70 else if a = 0x9028 then 0x20 else
    if a = 0x9031 then 0x80 else if a = 0x9038 then 0x01 else if a = 0x9042 then 0x01 else
    if a = 0x9049 then 0x04 else 0
  rd := [⟨0x8000, 1⟩, ⟨0x9000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x5000, 32⟩, ⟨0x6000, 32⟩, ⟨0x7000, 32⟩,
    ⟨0x10000, 8192⟩]

theorem key_implies : keyA.Implies (Spec.RsaKeyGen.keyContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre,
      stackArgs_ten, List.append_eq] at h
    sig_pre [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre,
      stackArgs_ten, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre,
      stackArgs_ten, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    intro s s' _ h
    sig_post [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_ten, List.append_eq]
    sig_reduce [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyA, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_ten, List.append_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    revert h2
    simp only [arg]
    generalize Spec.RsaKeyGen.keyOp _ _ _ _ = r
    rcases r with (f | ys) | u <;> first | exact id | simp
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyA, keyPub,
      keyLeak, keyRes, stackArgs_ten, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, hsp, fun i hi => ?_, hl⟩
    · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact a0
      · exact a1
      · exact a2
      · exact a3
      · exact a4
      · exact a5
      · exact a6
      · exact a7
      · exact a8
      · exact a9
  sat := by sig_implies_sat [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs,
    keyA, keyPre, stackArgs_ten, List.append_eq] [keySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using keySat

end VG.Proof.RsaKeyGen.AArch64.Key
