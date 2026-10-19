module

public import VerifiedGarbage.Proof.Rsa.Arm.CckCorrect
import VerifiedGarbage.Proof.Rsa.Arm.CckTaint
public import VerifiedGarbage.Proof.Rsa.Arm.KcFnCT
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Rsa.Arm.CvFail

/-! # `vg_rsa_check_crt_key` on ARMv7 is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CheckCrtKey
open VG VG.Arm VG.Proof.Rsa.Arm.KeyCheck VG.Impl.Rsa.Arm.KeyCheck

/-- Two runs that agree on `n`, `e`, the pointers and the lengths. -/
theorem pubF_of {s t : State} (sp : s.sp = t.sp)
    (bytes : (Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r0)) (s.gpr .r1).toNat ++
        Spec.Rsa.bytesAt s.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (t.gpr .r0)) (t.gpr .r1).toNat ++
        Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (t.gpr .r2)) (t.gpr .r3).toNat).map (·.toNat))
    (p0 : s.gpr .r0 = t.gpr .r0) (p1 : s.gpr .r1 = t.gpr .r1) (p2 : s.gpr .r2 = t.gpr .r2)
    (p3 : s.gpr .r3 = t.gpr .r3) {nA : Nat} (args : ∀ i < nA, stackArg s i = stackArg t i) : PubF nA s t := by
  have b := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 bytes
  obtain ⟨hn, he⟩ := List.append_inj b (by
    rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length, VG.Proof.Rsa.Arm.CrtValues.bytesAt_length, p1])
  exact ⟨sp, hn, he, p0, p1, p2, p3, args⟩

theorem cck_body_ct : RelCT isa
    (LiftB (PubF 12) fun a σ v s => s = σ ∧ FnBase 12 10 insC a σ ∧ BodyIn (geo 10 a) v s) crtBody
    (LiftB (PubF 12) fun a σ _ t => FnBase 12 10 insC a σ ∧ ∃ A live c, Stg (geo 10 a) σ A live c t) :=
  (crtBody_ct (Pub := PubF 12) (gf := geo 10) (fun _ _ p => p.geo_eq (by decide))
    (fun a σ => FnBase 12 10 insC a σ)).mono (fun _ _ h => h)
    fun _ _ h => LiftB.mono (fun _ _ _ _ ⟨x, _, _, _, _, _, _, _, ht⟩ => ⟨x, _, _, _, ht⟩) h

theorem cck_contract_ct : ConstantTime isa (Spec.Rsa.checkCrtKeyContract abi 0).pre
    (Spec.Rsa.checkCrtKeyContract abi 0).pub VG.Impl.Rsa.Arm.CheckCrtKey.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := cck_pre s hs
  have it := cck_pre t ht
  sig_pub [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hp
  have args : ∀ i < 12, stackArg s i = stackArg t i := fun i hi =>
    match i, hi with
    | 0, _ => a0 | 1, _ => a1 | 2, _ => a2 | 3, _ => a3 | 4, _ => a4 | 5, _ => a5
    | 6, _ => a6 | 7, _ => a7 | 8, _ => a8 | 9, _ => a9 | 10, _ => a10 | 11, _ => a11
    | _ + 12, h => absurd h (by omega)
  rw [code_eq] at e1 e2
  exact (fn_ct (vf := vC) (by decide) (by decide) entry_taint restore_taint (fun σ _ => cck_hv σ)
    (fun _ h => cck_hA h) cck_body_ct s t tr1 tr2 u v ⟨is, it, pubF_of sp bytes p0 p1 p2 p3 args⟩ e1 e2).1

/-- A 64-byte modulus, one-byte exponent and factors, the working space at
`0x4000`, and the stack arguments at `0x8000`. -/
def cckSatState : State where
  gpr r := match r with
    | .r0 => 0x2000 | .r1 => 64 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x31 else if a = 0x8004 then 1 else if a = 0x8009 then 0x32
    else if a = 0x800C then 1 else if a = 0x8011 then 0x33 else if a = 0x8014 then 1
    else if a = 0x8019 then 0x34 else if a = 0x801C then 1 else if a = 0x8021 then 0x35
    else if a = 0x8024 then 1 else if a = 0x8029 then 0x40 else if a = 0x802C then 0x20
    else if a = 0x802D then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩, ⟨0x3500, 1⟩,
    ⟨0x8000, 48⟩]
  wr := [⟨0x4000, 8448⟩]

theorem cck_contract_sat : ∃ s, (Spec.Rsa.checkCrtKeyContract abi 0).pre s := by
  sig_implies_sat [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
    [cckSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using cckSatState

/-- `vg_rsa_check_crt_key`. -/
theorem check_crt_key_verified :
    Verified target VG.Impl.Rsa.Arm.CheckCrtKey.code (Spec.Rsa.checkCrtKeyContract abi 0) :=
  ⟨cck_contract_correct, cck_contract_ct, cck_contract_sat⟩

end VG.Proof.Rsa.Arm.CheckCrtKey
