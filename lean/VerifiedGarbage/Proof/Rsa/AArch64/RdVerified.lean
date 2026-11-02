module

import VerifiedGarbage.Proof.Rsa.AArch64.RdCT6
public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.AArch64.RecoverDet
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.AArch64.RdCode
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# `vg_rsa_recover_primes_det` on AArch64: verified against the shared contract

`rdA` states the shared contract on the registers and the stack
(`rd_implies`); with correctness (`rdCode_correct`) and constant time
(`rdCode_constantTime`), `RecoverDet.code` is verified (`rd_verified`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

/-- A state meeting `rpA.pre`: a 512-bit modulus, one-byte exponents, and
the stack arguments at `0x6000`. -/
def rpSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1100 | .x3 => 64 | .x4 => 0x2000 | .x5 => 64 | .x6 => 0x3000
    | .x7 => 1 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6018 then 0x20
    else if a = 0x6001 then 0x31 else if a = 0x6008 then 1 else if a = 0x6011 then 0x80
    else if a = 0x6019 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x6000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x8000, 8448⟩]

theorem rd_implies : rdA.Implies (Spec.Rsa.recoverPrimesDetContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdA, rpA, stackArgs_four,
      List.append_eq] at h
    sig_pre [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdA, rpA, stackArgs_four,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdA, rpA, stackArgs_four,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals first | with_reducible assumption | (simp only [Spec.Rsa.lenValid] at *; omega)
  post := by sig_implies_post [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdA,
    stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdA, stackArgs_four,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3⟩ := h
    have hm := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
    obtain ⟨hn, he⟩ := List.append_inj hm (by rw [bytesAt_length, bytesAt_length, r5])
    refine ⟨?_, hsp, by rw [stackArgs_four, stackArgs_four, a0, a1, a2, a3], hn, he⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by sig_implies_sat [Spec.Rsa.recoverPrimesDetContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rdA, rpA,
    stackArgs_four, List.append_eq] [rpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rpSatState

/-- `vg_rsa_recover_primes_det`. -/
theorem rd_verified [InvLaw] :
    Verified target VG.Impl.Rsa.AArch64.RecoverDet.code (Spec.Rsa.recoverPrimesDetContract abi) :=
  Verified.of_correct rdCode_correct rdCode_constantTime rd_implies

end VG.Proof.Rsa.AArch64.Rd
