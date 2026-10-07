import VerifiedGarbage.Proof.Rsa.AArch64.PrivCallees

/-!
# RSA with the CRT on AArch64: the shared contract

`crtA` (`Proof/Rsa/AArch64/PrivCallees.lean`) states the shared contract of
`vg_rsa_private_crt` on the registers and the stack (`crt_implies`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64
open VG.Proof.Rsa.AArch64 (crtA stackArgs_ten)

/-- A state meeting `crtA.pre`: a 64-byte modulus and input, one-byte
primes, exponents and `qInv`, and the stack arguments at `0x10000`. -/
def crtSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 64
    | .x6 => 0x4000 | .x7 => 1 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 0x41 else if a = 0x10008 then 1 else if a = 0x10011 then 0x42
    else if a = 0x10018 then 1 else if a = 0x10021 then 0x43 else if a = 0x10028 then 1
    else if a = 0x10031 then 0x44 else if a = 0x10038 then 1 else if a = 0x10042 then 0x02
    else if a = 0x10049 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x10000, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8192⟩]

theorem crt_implies : crtA.Implies (Spec.Rsa.privateCrtContract abi 0) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtA, stackArgs_ten,
      List.append_eq] at h
    sig_pre [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtA, stackArgs_ten,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtA, stackArgs_ten,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtA,
      stackArgs_ten, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtA, stackArgs_ten,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, hsp, by simp only [stackArgs_ten, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtA,
      stackArgs_ten, List.append_eq] [crtSatState, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using crtSatState

end VG.Proof.Bignum.AArch64
