import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCTCode
import VerifiedGarbage.Proof.Rsa.AArch64.CkVerified

/-!
# `vg_rsa_check_crt_key` on AArch64: verified against the shared contract

`ckcA` states the shared contract on the registers and the stack
(`ckc_implies`); with correctness (`ckcCode_correct`) and constant time
(`ckcCode_constantTime`), `CheckCrtKey.code` is verified (`ckc_verified`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64

/-- A state meeting `ckcA.pre`: a 512-bit modulus, one-byte values, and the
stack arguments at `0x6000`. -/
def ckcSatState : State where
  gpr r := match r with
    | .x0 => 0x2000 | .x1 => 64 | .x2 => 0x2100 | .x3 => 1 | .x4 => 0x2200 | .x5 => 1 | .x6 => 0x2300
    | .x7 => 1 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6001 then 0x24 else if a = 0x6008 then 1 else if a = 0x6011 then 0x25
    else if a = 0x6018 then 1 else if a = 0x6021 then 0x26 else if a = 0x6028 then 1
    else if a = 0x6031 then 0x80 else if a = 0x6039 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x2200, 1⟩, ⟨0x2300, 1⟩, ⟨0x2400, 1⟩, ⟨0x2500, 1⟩, ⟨0x2600, 1⟩,
    ⟨0x6000, 64⟩]
  wr := [⟨0x8000, 8192⟩]

theorem ckcStackArgs (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

theorem ckc_implies : ckcA.Implies (Spec.Rsa.checkCrtKeyContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckcA, ckcStackArgs,
      List.append_eq] at h
    sig_pre [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckcA, ckcStackArgs,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckcA, ckcStackArgs,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckcA, ckcKeyOf,
      ckcStackArgs, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckcA, ckcStackArgs,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    rw [List.map_append, List.map_append] at hl
    obtain ⟨hn, he⟩ := List.append_inj hl (by simp [Spec.Rsa.bytesAt, r1])
    refine ⟨?_, hsp, by rw [ckcStackArgs, ckcStackArgs, a0, a1, a2, a3, a4, a5, a6, a7],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn,
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, ckcA, ckcStackArgs,
      List.append_eq] [ckcSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using ckcSatState

/-- `vg_rsa_check_crt_key`. -/
theorem ckc_verified :
    Verified target VG.Impl.Rsa.AArch64.CheckCrtKey.code (Spec.Rsa.checkCrtKeyContract abi) :=
  Verified.of_correct ckcCode_correct ckcCode_constantTime ckc_implies

end VG.Proof.Rsa.AArch64
