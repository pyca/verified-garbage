module
-- separate module: it builds in parallel with the batched inverse's proofs (`InvInstance`, which imports the divstep algebra), which only `Instances` brings in

import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTMain
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Code
public import VerifiedGarbage.Proof.Rsa.X86_64.InvLaw
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

theorem stackArgs_six (s : State) :
    List.map (stackArg s) (List.range 6) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5] := rfl

/-- A state meeting `rdContract.pre`: a 512-bit modulus, one-byte exponents,
and the stack arguments at `0x6008`. -/
def rpSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x1100 | .rcx => 64 | .r8 => 0x2000 | .r9 => 64
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6030 then 0x20
    else if a = 0x6009 then 0x30 else if a = 0x6010 then 1 else if a = 0x6019 then 0x31
    else if a = 0x6020 then 1 else if a = 0x6029 then 0x80 else if a = 0x6031 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x6008, 48⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x8000, 8448⟩]

theorem rd_implies : rdContract.Implies (Spec.Rsa.recoverPrimesDetContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract, rpPre,
      stackArgs_six, List.append_eq] at h
    sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract, rpPre,
      stackArgs_six, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract, rpPre,
      stackArgs_six, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | (simp only [Spec.Rsa.lenValid] at *; omega)
  post := by sig_implies_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract,
    stackArgs_six, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract, stackArgs_six,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5⟩ := h
    have hm := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
    obtain ⟨hn, he⟩ := List.append_inj hm (by rw [bytesAt_length, bytesAt_length, h9])
    refine ⟨?_, a0, a1, a2, a3, a4, a5, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesDetSig, abi, argRegs, rdContract,
    rpPre, stackArgs_six, List.append_eq] [rpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rpSatState

/-- `vg_rsa_recover_primes_det`, given that its code never loads MXCSR (which
the registration file evaluates). -/
theorem rd_verified [InvLaw] (hmx : RecoverDet.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi) :=
  Verified.of_correct (rdCode_correct hmx) rdCode_constantTime rd_implies

end VG.Proof.Rsa.X86_64.Rd
