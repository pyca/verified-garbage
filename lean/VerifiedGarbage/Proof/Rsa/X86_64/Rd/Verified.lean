module

import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTMain
import VerifiedGarbage.Proof.Rsa.X86_64.RpVerified
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Code
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
public import VerifiedGarbage.Proof.Rsa.X86_64.InvInstance
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_rsa_recover_primes_det` on x86-64: verified against the shared contract

`rdContract` states the shared contract on the registers and the stack
(`rd_implies`); with correctness (`rdCode_correct`) and constant time
(`rdCode_constantTime`), `RecoverDet.code` is verified (`rd_verified`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem rd_implies : rdContract.Implies (Spec.Rsa.recoverPrimesDetContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdContract, rpContract,
      stackArgs_six, List.append_eq] at h
    sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdContract, rpContract,
      stackArgs_six, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdContract, rpContract,
      stackArgs_six, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | (simp only [Spec.Rsa.lenValid] at *; omega)
  post := by sig_implies_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdContract,
    stackArgs_six, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdContract, stackArgs_six,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5⟩ := h
    have hm := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
    obtain ⟨hn, he⟩ := List.append_inj hm (by rw [bytesAt_length, bytesAt_length, h9])
    refine ⟨?_, a0, a1, a2, a3, a4, a5, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdContract,
    rpContract, stackArgs_six, List.append_eq] [rpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rpSatState

/-- `vg_rsa_recover_primes_det`, given that its code never loads MXCSR (which
the registration file evaluates). -/
theorem rd_verified [InvLaw] (hmx : RecoverDet.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi) :=
  Verified.of_correct (rdCode_correct hmx) rdCode_constantTime rd_implies

/-- `vg_rsa_recover_primes_det`, with the batched inverse's instance. -/
theorem recoverDet_verified :
    Verified target RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi) :=
  rd_verified (by decide +kernel)

end VG.Proof.Rsa.X86_64.Rd
