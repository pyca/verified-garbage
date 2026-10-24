module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcContract
public import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_check_key` and `vg_rsa_check_crt_key` on PPC64LE: the shared contracts imply `ckP` and `cckP`
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

theorem stackArgs_eight (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

/-- A state meeting `ckP.pre`: a 512-bit modulus, one-byte other numbers,
and the stack arguments at `sp + 96 = 0x6060`. -/
def ckSatState : State where
  gpr r := match r with
    | .r3 => 0x2000 | .r4 => 64 | .r5 => 0x3000 | .r6 => 1 | .r7 => 0x3100 | .r8 => 1 | .r9 => 0x3200
    | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x6000
  mem a := if a = 0x6061 then 0x33 else if a = 0x6068 then 1 else if a = 0x6071 then 0x34
    else if a = 0x6078 then 1 else if a = 0x6081 then 0x35 else if a = 0x6088 then 1
    else if a = 0x6091 then 0x36 else if a = 0x6098 then 1 else if a = 0x60a1 then 0x80
    else if a = 0x60a8 then 0x20 else if a = 0x60a9 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x3600, 1⟩, ⟨0x6060, 80⟩]
  wr := [⟨0x8000, 8448⟩]

/-- A state meeting `cckP.pre`. -/
def cckSatState : State where
  gpr r := match r with
    | .r3 => 0x2000 | .r4 => 64 | .r5 => 0x3000 | .r6 => 1 | .r7 => 0x3200 | .r8 => 1 | .r9 => 0x3300
    | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x6000
  mem a := if a = 0x6061 then 0x34 else if a = 0x6068 then 1 else if a = 0x6071 then 0x35
    else if a = 0x6078 then 1 else if a = 0x6081 then 0x36 else if a = 0x6088 then 1
    else if a = 0x6091 then 0x80 else if a = 0x6098 then 0x20 else if a = 0x6099 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩, ⟨0x3600, 1⟩,
    ⟨0x6060, 64⟩]
  wr := [⟨0x8000, 8448⟩]

theorem ck_implies : ckP.Implies (Spec.Rsa.checkKeyContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckP, stackArgs_ten,
      List.append_eq] at h
    sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckP, stackArgs_ten,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckP, stackArgs_ten,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | omega
  post := by
    sig_implies_post [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckP, stackArgs_ten,
      List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckP, stackArgs_ten,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_ten, stackArgs_ten, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9], hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, ckP, stackArgs_ten,
      List.append_eq] [ckSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using ckSatState

theorem cck_implies : cckP.Implies (Spec.Rsa.checkCrtKeyContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, cckP, stackArgs_eight,
      List.append_eq] at h
    sig_pre [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, cckP, stackArgs_eight,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, cckP, stackArgs_eight,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | omega
  post := by
    sig_implies_post [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, cckP,
      stackArgs_eight, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, cckP, stackArgs_eight,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
    refine ⟨?_, hsp, by rw [stackArgs_eight, stackArgs_eight, a0, a1, a2, a3, a4, a5, a6, a7], hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, cckP,
      stackArgs_eight, List.append_eq] [cckSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using cckSatState

end VG.Proof.Rsa.PPC64LE.KeyCheck
