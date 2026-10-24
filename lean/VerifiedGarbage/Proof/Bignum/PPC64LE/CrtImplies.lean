module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtFn
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# The RSA private-key operation on PPC64LE: the shared contract

`fnContract` states the shared contract of `vg_rsa_private_crt` on the
registers and the stack (`crt_implies`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE

/-- A state meeting `fnContract.pre`: a 64-byte modulus and input, one-byte
primes, exponents and `qInv`, and the stack arguments at `0x10060`. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 64 | .r5 => 0x2000 | .r6 => 64 | .r7 => 0x3000 | .r8 => 64
    | .r9 => 0x4000 | .r10 => 1 | _ => 0
  lr := 0
  sp := 0x10000
  mem a := if a = 0x100A8 then 0x20
    else if a = 0x10061 then 0x41 else if a = 0x10068 then 1 else if a = 0x10071 then 0x42
    else if a = 0x10078 then 1 else if a = 0x10081 then 0x43 else if a = 0x10088 then 1
    else if a = 0x10091 then 0x44 else if a = 0x10098 then 1 else if a = 0x100A2 then 0x02
    else if a = 0x100A9 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 64⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x10060, 80⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem crt_implies : fnContract.Implies (Spec.Rsa.privateCrtContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, fnContract, stackArgs_ten,
      List.append_eq] at h
    sig_pre [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, fnContract, stackArgs_ten,
      List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, fnContract, stackArgs_ten,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, fnContract,
      stackArgs_ten, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, fnContract, stackArgs_ten,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
    refine ⟨?_, hsp, by simp only [stackArgs_ten, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9],
      (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  sat := by
    sig_implies_sat [Spec.Rsa.privateCrtContract, Spec.Rsa.privateCrtSig, abi, argRegs, fnContract,
      stackArgs_ten, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using satState

end VG.Proof.Bignum.PPC64LE.Crt
