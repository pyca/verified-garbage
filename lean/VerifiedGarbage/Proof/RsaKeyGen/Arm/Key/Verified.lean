module

import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Top4
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Result
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Top2
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.RsaKeyGen.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Top3
import VerifiedGarbage.Proof.Rsa.Arm.CvFail

/-! # `vg_rsa_keygen_key` on ARMv7 is verified against the shared contract -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm
open VG.Impl.RsaKeyGen.Arm.Key (code)
open VG.Proof.Bignum.Arm (pcPushed)

section
variable {s : State}

/-- The result of the call, from the caller's memory. -/
theorem res_mk (h : CIn s) : res (mkP s) (sx s) = Spec.RsaKeyGen.keyOp (stackArg s 1).toNat
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 1).toNat) := by
  have bP : Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 0)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat :=
    h.bytes (R := cP s) h.Fp (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  have bQ : Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 2)) (stackArg s 1).toNat =
      Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 1).toNat :=
    h.bytes (R := (mkP s).rQ) (by rw [h.rQ]; exact h.Fq) (Nat.le_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide)))
  show Spec.RsaKeyGen.keyOp (stackArg s 1).toNat (mkP s).eB
    (Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt (pcPushed s).mem (State.addr (stackArg s 2)) (stackArg s 1).toNat) = _
  rw [bP, bQ]; rfl

theorem resv_ok {P : KP} {σ : State} {ys : List (List Byte)} (h : resv P σ = .inl (.ok ys)) : ys = outv P σ := by
  unfold resv at h
  split at h
  · cases h
  · split at h
    · injection h with h; injection h with h; exact h.symm
    · cases h

end

theorem key_contract_correct [VG.Proof.Rsa.Arm.Keys.InvLaw] (s : State) (h : (Spec.RsaKeyGen.keyContract abi 56).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ (Spec.RsaKeyGen.keyContract abi 56).post s t := by
  have hc := cin_of_pre s h
  obtain ⟨tr, t, run, preserved, r0, outs⟩ := key_ok hc
  refine ⟨tr, t, run, preserved, ?_⟩
  have e := (res_mk hc).symm.trans (res_spec (in_k hc))
  simp only [State.addr] at e
  sig_post [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right, e, hc.nl]
  refine ⟨r0, ?_⟩
  unfold outE at outs
  rcases hres : resv (mkP s) (sx s) with (f | ys) | u
  · simp only [hres] at outs
    exact ⟨outs 0 (by decide), outs 1 (by decide), outs 2 (by decide), outs 3 (by decide), outs 4 (by decide),
      outs 5 (by decide), outs 6 (by decide)⟩
  · have hy := resv_ok hres
    simp only [hres] at outs
    subst hy
    show (List.range 7).map (fun i => Spec.Rsa.bytesAt t.mem (State.addr (oPtr (mkP s) i)) (oLen (mkP s) i)) = _
    rw [List.map_congr_left (fun i hi => outs i (List.mem_range.mp hi))]
    rfl
  · simp only [hres] at outs
    exact ⟨outs 0 (by decide), outs 1 (by decide), outs 2 (by decide), outs 3 (by decide), outs 4 (by decide),
      outs 5 (by decide), outs 6 (by decide)⟩

/-- Calls with the same public arguments, `e` and status have the same
public parameters. -/
theorem mkP_eq {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (a0 : stackArg s 0 = stackArg t 0) (a1 : stackArg s 1 = stackArg t 1) (a2 : stackArg s 2 = stackArg t 2)
    (a4 : stackArg s 4 = stackArg t 4) (a6 : stackArg s 6 = stackArg t 6) (a8 : stackArg s 8 = stackArg t 8)
    (a10 : stackArg s 10 = stackArg t 10) (a11 : stackArg s 11 = stackArg t 11)
    (a12 : stackArg s 12 = stackArg t 12) (a13 : stackArg s 13 = stackArg t 13)
    (he : Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 10)) (stackArg t 11).toNat)
    (hst : Spec.RsaKeyGen.keyStatus (Spec.RsaKeyGen.keyOp (stackArg s 1).toNat
        (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 10)) (stackArg s 11).toNat)
        (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 1).toNat)) =
      Spec.RsaKeyGen.keyStatus (Spec.RsaKeyGen.keyOp (stackArg t 1).toNat
        (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 10)) (stackArg t 11).toNat)
        (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 0)) (stackArg t 1).toNat)
        (Spec.Rsa.bytesAt t.mem (State.addr (stackArg t 2)) (stackArg t 1).toNat))) :
    mkP s = mkP t := by
  unfold mkP
  rw [hst, he, sp, p0, p2, a0, a1, a2, a4, a6, a8, a10, a11, a12, a13]

theorem key_contract_ct [VG.Proof.Rsa.Arm.Keys.InvLaw] : ConstantTime isa (Spec.RsaKeyGen.keyContract abi 56).pre
    (Spec.RsaKeyGen.keyContract abi 56).pub code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := cin_of_pre s hs
  have it := cin_of_pre t ht
  sig_pub [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, _, a0, a1, a2, _, a4, _, a6, _, a8, _, a10, a11, a12, a13⟩ := hp
  obtain ⟨b1, b2⟩ := List.append_inj bytes (by
    simp only [List.length_map, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; rw [a11])
  have he := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 b1
  exact (key_ct s t tr1 tr2 u v ⟨is, it, sp,
    mkP_eq sp p0 p2 a0 a1 a2 a4 a6 a8 a10 a11 a12 a13 he (List.singleton_inj.1 b2)⟩ e1 e2).1

/-- 32-byte primes, a one-byte exponent, the outputs at `0x1000`–`0x1600`,
`e` at `0x1700`, the working space at `0x4000`, and the stack arguments at
`0x8000`. -/
def keySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 64 | .r2 => 0x1100 | .r3 => 64 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x12 else if a = 0x8004 then 0x20 else if a = 0x8009 then 0x13
    else if a = 0x800C then 0x20 else if a = 0x8011 then 0x14 else if a = 0x8014 then 0x20
    else if a = 0x8019 then 0x15 else if a = 0x801C then 0x20 else if a = 0x8021 then 0x16
    else if a = 0x8024 then 0x20 else if a = 0x8029 then 0x17 else if a = 0x802C then 1
    else if a = 0x8031 then 0x40 else if a = 0x8034 then 0x20 else if a = 0x8035 then 0x04 else 0
  rd := [⟨0x1700, 1⟩, ⟨0x8000, 56⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 64⟩, ⟨0x1200, 32⟩, ⟨0x1300, 32⟩, ⟨0x1400, 32⟩, ⟨0x1500, 32⟩, ⟨0x1600, 32⟩,
    ⟨0x4000, 8448⟩]

theorem key_contract_sat : ∃ s, (Spec.RsaKeyGen.keyContract abi 56).pre s := by
  sig_implies_sat [Spec.RsaKeyGen.keyContract, Spec.RsaKeyGen.keySig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
    [keySatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.RsaKeyGen.primeLenValid, Spec.Rsa.scratchWords]
    using keySatState

/-- `vg_rsa_keygen_key`. -/
theorem key_verified [VG.Proof.Rsa.Arm.Keys.InvLaw] : Verified target code (Spec.RsaKeyGen.keyContract abi 56) :=
  ⟨key_contract_correct, key_contract_ct, key_contract_sat⟩

end VG.Proof.RsaKeyGen.Arm.Key
