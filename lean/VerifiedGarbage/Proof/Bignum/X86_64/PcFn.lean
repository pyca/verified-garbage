import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost

/-!
# `vg_rsa_public_precompute` on x86-64: its shared contract, with 8 bytes of stack

`pcContract` implies `Spec.Rsa.publicPrecomputeContract` with the stack its
calls of Montgomery multiplication use, a return address
(`precompute_implies8`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64.MontFn

theorem precompute_implies8 : pcContract.Implies (Spec.Rsa.publicPrecomputeContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9⟩ := h
    refine ⟨?_, (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] [pcSatState] using pcSatState

end VG.Proof.Bignum.X86_64
