module
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw

import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Top5
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Top1
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.RsaKeyGen.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Top4
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.MillerRabin.Arm.Top
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Trial

/-! # `vg_rsa_keygen_candidate` on ARMv7 is verified against the shared contract

For any implementation of the Miller–Rabin round it calls (`RoundImpl`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm
open VG.Impl.RsaKeyGen.Arm.Candidate (code)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem cand_contract_correct [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) (s : State) (h : (Spec.RsaKeyGen.candidateContract abi 112).pre s) :
    ∃ tr t, Exec isa (code v.name v.code) s tr t ∧ abiPreserved s t ∧
      (Spec.RsaKeyGen.candidateContract abi 112).post s t := by
  have hc := cin_of_pre s h
  obtain ⟨tr, t, run, preserved, r0, outs, used⟩ := cand_ok v hc
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact ⟨r0, outs, used⟩

/-- Calls with the same public arguments, `e` and leak have the same public parameters. -/
theorem mkP_eq {s t : State} (hs : CIn s) (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0)
    (p1 : s.gpr .r1 = t.gpr .r1) (p2 : s.gpr .r2 = t.gpr .r2) (p3 : s.gpr .r3 = t.gpr .r3)
    (a0 : stackArg s 0 = stackArg t 0) (a1 : stackArg s 1 = stackArg t 1) (a2 : stackArg s 2 = stackArg t 2)
    (a3 : stackArg s 3 = stackArg t 3) (a4 : stackArg s 4 = stackArg t 4) (a5 : stackArg s 5 = stackArg t 5)
    (a6 : stackArg s 6 = stackArg t 6)
    (he : Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (t.gpr .r3)) (stackArg t 0).toNat)
    (hl : Spec.RsaKeyGen.candidateLeak (s.gpr .r1).toNat
        (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
        (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat)
        (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 4).toNat) =
      Spec.RsaKeyGen.candidateLeak (t.gpr .r1).toNat
        (Spec.Rsa.bytesAt t.mem (State.addr (t.gpr .r3)) (stackArg t 0).toNat)
        (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 1)) (stackArg t 2).toNat)
        (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 3)) (stackArg t 4).toNat)) :
    mkP s = mkP t := by
  have hL := hs.valid.1
  unfold mkP
  rw [he] at hl ⊢
  rw [p1, a1, a2, a3, a4] at hl ⊢
  rw [sp, p0, p2, p3, a0, a5, a6]
  by_cases hk : (t.gpr .r1).toNat ≤ (stackArg t 4).toNat
  · rw [VG.Proof.RsaKeyGen.ite_t hk, VG.Proof.RsaKeyGen.ite_t hk]
    rw [VG.Proof.RsaKeyGen.candidateLeak_eq, VG.Proof.RsaKeyGen.candidateLeak_eq] at hl
    rw [VG.Proof.RsaKeyGen.schedOf_eq (by rw [← p1] at *; omega)
      (by rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length])
      (by rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; exact hk) hl]
  · rw [VG.Proof.RsaKeyGen.ite_f hk, VG.Proof.RsaKeyGen.ite_f hk]

theorem cand_contract_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) : ConstantTime isa (Spec.RsaKeyGen.candidateContract abi 112).pre
    (Spec.RsaKeyGen.candidateContract abi 112).pub (code v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := cin_of_pre s hs
  have it := cin_of_pre t ht
  sig_pub [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, a0, a1, a2, a3, a4, a5, a6⟩ := hp
  obtain ⟨b1, b2⟩ := List.append_inj bytes (by
    simp only [List.length_map, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; rw [a0])
  have he := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 b1
  exact (cand_ct v s t tr1 tr2 u w ⟨is, it, sp,
    mkP_eq is sp p0 p1 p2 p3 a0 a1 a2 a3 a4 a5 a6 he b2⟩ e1 e2).1

/-- 32-octet primes, a one-octet exponent, no `p` and no `rand`: `out` at
`0x1000`, `used` at `0x1100`, `e` at `0x1200`, the working space at
`0x4000`, and the stack arguments at `0x8000`. -/
def candSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 32 | .r2 => 0x1100 | .r3 => 0x1200 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8000 then 1 else if a = 0x8005 then 0x13 else if a = 0x800D then 0x14
    else if a = 0x8015 then 0x40 else if a = 0x8018 then 0x20 else if a = 0x8019 then 0x02 else 0
  rd := [⟨0x1200, 1⟩, ⟨0x1300, 0⟩, ⟨0x1400, 0⟩, ⟨0x8000, 28⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x1100, 8⟩, ⟨0x4000, 4352⟩]

theorem cand_contract_sat : ∃ s, (Spec.RsaKeyGen.candidateContract abi 112).pre s := by
  sig_implies_sat [Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
    [candSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.RsaKeyGen.primeLenValid, Spec.Rsa.scratchWords]
    using candSatState

/-- `vg_rsa_keygen_candidate`, calling the round `v`. -/
theorem cand_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] (v : RoundImpl) :
    Verified target (code v.name v.code) (Spec.RsaKeyGen.candidateContract abi 112) :=
  ⟨cand_contract_correct v, cand_contract_ct v, cand_contract_sat⟩

end VG.Proof.RsaKeyGen.Arm.Cand
