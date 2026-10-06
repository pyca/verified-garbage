import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# An RSA key from its primes on x86-64: the shared contract implies `keyCtr`
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-- A state meeting the precondition: 32-byte primes, a one-byte `e`, the
stack arguments at `0x9008`. -/
def keySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 32
    | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x9009 then 0x40 else if a = 0x9010 then 0x20 else if a = 0x9019 then 0x50 else
    if a = 0x9020 then 0x20 else if a = 0x9029 then 0x60 else if a = 0x9030 then 0x20 else
    if a = 0x9039 then 0x70 else if a = 0x9040 then 0x20 else if a = 0x9049 then 0x80 else
    if a = 0x9050 then 0x01 else if a = 0x905a then 0x01 else if a = 0x9061 then 0x04 else 0
  rd := [⟨0x8000, 1⟩, ⟨0x9008, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩, ⟨0x5000, 32⟩, ⟨0x6000, 32⟩, ⟨0x7000, 32⟩,
    ⟨0x10000, 8192⟩]

theorem key_implies : keyCtr.Implies (Spec.RsaKeyGen.keyContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre,
      stackArgs_twelve, List.append_eq] at h
    sig_pre [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre,
      stackArgs_twelve, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre,
      stackArgs_twelve, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    intro s s' _ h
    sig_post [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_twelve, List.append_eq]
    sig_reduce [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_twelve, List.append_eq] at h
    sig_simp [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPre, keyPost, keyRes,
      keyOuts, stackArgs_twelve, List.append_eq] [] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1, ?_⟩
    revert h2
    simp only [arg]
    generalize Spec.RsaKeyGen.keyOp _ _ _ _ = r
    rcases r with (f | ys) | u <;> first | exact id | simp
  pub := by
    intro s₁ s₂ _ _ h
    sig_pub [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, keyCtr, keyPub,
      keyLeak, keyRes, stackArgs_twelve, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    refine ⟨hdi, hsi, hdx, hcx, h8, h9, hsp, fun i hi => ?_, hl⟩
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11
      by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · exact a10
    · exact a11
  sat := by sig_implies_sat [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs,
    keyCtr, keyPre, stackArgs_twelve, List.append_eq] [keySat, stackArg, stackArgAddr, Mem.readW, Mem.read] using keySat

end VG.Proof.RsaKeyGen.X86_64.Key
