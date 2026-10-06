import VerifiedGarbage.Proof.Rsa.AArch64.RpCT8
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_recover_primes` on AArch64: verified against the shared contract

`rpA` states the shared contract on the registers and the stack
(`rp_implies`); with correctness (`rpCode_correct`) and constant time
(`rpCode_constantTime`), `Recover.code` is verified for any Montgomery
multiplication (`rp_verified`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

/-- A state meeting `rpA.pre`: a 512-bit modulus, one-byte exponents, and
the stack arguments at `0x6000`. -/
def rpSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1100 | .x3 => 64 | .x4 => 0x2000 | .x5 => 64 | .x6 => 0x3000
    | .x7 => 1 | _ => 0
  sp := 0x6000
  mem a := if a = 0x6001 then 0x31 else if a = 0x6008 then 1 else if a = 0x6011 then 0x80
    else if a = 0x6019 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x6000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x8000, 8192⟩]

theorem rp_implies : rpA.Implies (Spec.Rsa.recoverPrimesContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpA, stackArgs_four,
      List.append_eq] at h
    sig_pre [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpA, stackArgs_four,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpA, stackArgs_four,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpA,
    stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpA, stackArgs_four,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, r0, r1, r2, r3, r4, r5, r6, r7, a0, a1, a2, a3⟩ := h
    obtain ⟨hl₁, hc⟩ := List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)
    have hm := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl₁
    obtain ⟨hn, he⟩ := List.append_inj hm (by rw [bytesAt_length, bytesAt_length, r5])
    refine ⟨?_, hsp, by rw [stackArgs_four, stackArgs_four, a0, a1, a2, a3], hn, he, List.singleton_inj.mp hc⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩
  sat := by sig_implies_sat [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, rpA,
    stackArgs_four, List.append_eq] [rpSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using rpSatState

/-- `vg_rsa_recover_primes` with the Montgomery multiplication `M`. -/
theorem rp_verified (M : Mont) :
    Verified target (VG.Impl.Rsa.AArch64.Recover.code M.mm) (Spec.Rsa.recoverPrimesContract abi) :=
  Verified.of_correct (rpCode_correct M) (rpCode_constantTime M) rp_implies

end VG.Proof.Rsa.AArch64
