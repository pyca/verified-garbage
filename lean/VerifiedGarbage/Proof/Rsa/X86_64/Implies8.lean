import VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.Rsa.X86_64.RpVerified

/-!
# The x86-64 RSA functions' contracts, with 8 bytes of stack

What the functions that call `vg_rsa_mont_mul` meet: the shared contracts,
with the stack their call's return address uses (`Verified.of_inline`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem crt_implies8 : crtContract.Implies (Spec.Rsa.privateCrtContract abi 8) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq] at h
    sig_pre [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    refine ⟨?_, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, crtContract, stackArgs_twelve, List.append_eq] [crtSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using crtSatState

theorem rp_implies8 : rpContract.Implies (Spec.Rsa.recoverPrimesContract abi 8) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpContract, stackArgs_six,
      List.append_eq] at h
    sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpContract, stackArgs_six,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpContract, stackArgs_six,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpContract,
    stackArgs_six, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpContract, stackArgs_six,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5⟩ := h
    obtain ⟨hl₁, hc⟩ := List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)
    have hm := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl₁
    obtain ⟨hn, he⟩ := List.append_inj hm (by rw [bytesAt_length, bytesAt_length, h9])
    refine ⟨?_, a0, a1, a2, a3, a4, a5, hn, he, List.singleton_inj.mp hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpContract,
    stackArgs_six, List.append_eq] [rpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rpSatState

end VG.Proof.Rsa.X86_64
