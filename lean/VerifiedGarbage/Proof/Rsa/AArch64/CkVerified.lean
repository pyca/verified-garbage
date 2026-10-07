import VerifiedGarbage.Proof.Rsa.AArch64.CkCTCode
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_check_key` on AArch64: verified against the shared contract

`ckA` states the shared contract on the registers and the stack
(`ck_implies`); with correctness (`ckCode_correct`) and constant time
(`ckCode_constantTime`), `CheckKey.code` is verified (`ck_verified`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.CheckKey

/-- A state meeting `ckA.pre`: a 512-bit modulus, one-byte values, and the
stack arguments at `0x6000`. -/
def ckSatState : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 64 | .x2 => 0x2100 | .x3 => 1 | .x4 => 0x2200 | .x5 => 1 | .x6 => 0x2300
    | .x7 => 1 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6001 then 0x24 else if a = 0x6008 then 1 else if a = 0x6011 then 0x25
    else if a = 0x6018 then 1 else if a = 0x6021 then 0x26 else if a = 0x6028 then 1
    else if a = 0x6031 then 0x27 else if a = 0x6038 then 1 else if a = 0x6041 then 0x80
    else if a = 0x6049 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x2200, 1⟩, ⟨0x2300, 1⟩, ⟨0x2400, 1⟩, ⟨0x2500, 1⟩, ⟨0x2600, 1⟩,
    ⟨0x2700, 1⟩, ⟨0x6000, 80⟩]
  wr := [⟨0x8000, 8192⟩]

theorem stackArgs_ten' (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

theorem ck_implies : ckA.Implies (Spec.Rsa.checkKeyContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, stackArgs_ten', List.append_eq] at h
    sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, stackArgs_ten', List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, stackArgs_ten', List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, ckKeyOf, stackArgs_ten',
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, stackArgs_ten', List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    rw [List.map_append, List.map_append] at hl
    obtain ⟨hn, he⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, r1])
    refine ⟨?_, hsp, by rw [stackArgs_ten', stackArgs_ten', a0, a1, a2, a3, a4, a5, a6, a7, a8, a9],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn,
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckA, stackArgs_ten',
      List.append_eq] [ckSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using ckSatState

/-- `vg_rsa_check_key`. -/
theorem ck_verified : Verified target VG.Impl.Rsa.AArch64.CheckKey.code (Spec.Rsa.checkKeyContract abi) :=
  Verified.of_correct ckCode_correct ckCode_constantTime ck_implies

end VG.Proof.Rsa.AArch64
