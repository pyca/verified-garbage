module

import VerifiedGarbage.Proof.Rsa.Arm.RvTop5
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.RvTop1
public import VerifiedGarbage.Proof.Rsa.Arm.RvBody
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.RvTop4
import VerifiedGarbage.Proof.Rsa.Arm.CvFail

/-! # `vg_rsa_recover_primes` on ARMv7 is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Rsa.Arm.Recover

theorem rv_contract_correctWith (body : Prog isa) (bodyProof : BodyVerified body) (s : State) (h : (Spec.Rsa.recoverPrimesContract abi 56).pre s) :
    ∃ tr t, Exec isa (codeWith body) s tr t ∧ abiPreserved s t ∧ (Spec.Rsa.recoverPrimesContract abi 56).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := rv_okWith body bodyProof (cin_of_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact post

/-- Calls with the same public arguments, `n` and `e`, and number of
candidates tried have the same public parameters. -/
theorem mkP_eq {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (a0 : stackArg s 0 = stackArg t 0) (a1 : stackArg s 1 = stackArg t 1) (a2 : stackArg s 2 = stackArg t 2)
    (a3 : stackArg s 3 = stackArg t 3) (a4 : stackArg s 4 = stackArg t 4) (a5 : stackArg s 5 = stackArg t 5)
    (a6 : stackArg s 6 = stackArg t 6) (a7 : stackArg s 7 = stackArg t 7)
    (hn : Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 0)) (stackArg t 1).toNat)
    (he : Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 2)) (stackArg t 3).toNat)
    (ht : (Spec.Rsa.primesKey (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat)).2 =
      (Spec.Rsa.primesKey (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 0)) (stackArg t 1).toNat)
      (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 2)) (stackArg t 3).toNat)
      (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 4)) (stackArg t 5).toNat)).2) :
    mkP s = mkP t := by
  unfold mkP
  rw [ht, hn, he, sp, p0, p2, a0, a1, a2, a3, a4, a5, a6, a7]

theorem rv_contract_ctWith (body : Prog isa) (bodyProof : BodyVerified body) : ConstantTime isa (Spec.Rsa.recoverPrimesContract abi 56).pre
    (Spec.Rsa.recoverPrimesContract abi 56).pub (codeWith body) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := cin_of_pre s hs
  have it := cin_of_pre t ht
  sig_pub [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, _, a0, a1, a2, a3, a4, a5, a6, a7⟩ := hp
  have len := congrArg List.length bytes
  simp only [List.length_append, List.length_map, List.length_singleton,
    VG.Proof.Rsa.Arm.CrtValues.bytesAt_length] at len
  obtain ⟨b1, b2⟩ := List.append_inj bytes (by
    simp only [List.length_map, List.length_append, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; omega)
  have b3 := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 b1
  obtain ⟨hn, he⟩ := List.append_inj b3 (by
    simp only [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; rw [a1])
  exact (rv_ctWith body bodyProof s t tr1 tr2 u v ⟨is, it, sp,
    mkP_eq sp p0 p2 a0 a1 a2 a3 a4 a5 a6 a7 hn he (List.singleton_inj.1 b2), a0, a1⟩ e1 e2).1

/-- A 64-byte modulus, one-byte exponents, the outputs at `0x1000` and
`0x1100`, the working space at `0x4000`, and the stack arguments at
`0x8000`. -/
def rvSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x20 else if a = 0x8004 then 0x40 else if a = 0x8009 then 0x30
    else if a = 0x800C then 1 else if a = 0x8011 then 0x31 else if a = 0x8014 then 1
    else if a = 0x8019 then 0x40 else if a = 0x801C then 0x20 else if a = 0x801D then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x8000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x4000, 8448⟩]

theorem rv_contract_sat : ∃ s, (Spec.Rsa.recoverPrimesContract abi 56).pre s := by
  sig_implies_sat [Spec.Rsa.recoverPrimesContract, Spec.Rsa.recoverPrimesSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
    [rvSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using rvSatState

/-- Either search is verified through the same ABI and public contract. -/
theorem recover_primesWith_verified (body : Prog isa) (bodyProof : BodyVerified body) :
    Verified target (codeWith body) (Spec.Rsa.recoverPrimesContract abi 56) :=
  ⟨rv_contract_correctWith body bodyProof, rv_contract_ctWith body bodyProof, rv_contract_sat⟩

/-- `vg_rsa_recover_primes`. -/
theorem recover_primes_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] : Verified target code (Spec.Rsa.recoverPrimesContract abi 56) :=
  recover_primesWith_verified (.ite .eq valid fail) body_vp

end VG.Proof.Rsa.Arm.Recover
