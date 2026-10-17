module

public import VerifiedGarbage.Proof.Rsa.Arm.CkCorrect
public import VerifiedGarbage.Proof.Rsa.Arm.CkTaint
public import VerifiedGarbage.Proof.Rsa.Arm.CckVerified
public import VerifiedGarbage.Proof.Rsa.Arm.KcFnCT
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.TCB.Arm.Target
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_check_key` on ARMv7 is verified against the shared RSA contract -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CheckKey
open VG VG.Arm VG.Proof.Rsa.Arm.KeyCheck VG.Impl.Rsa.Arm.KeyCheck

theorem ck_body_ct : RelCT isa
    (LiftB (PubF 14) fun a σ v s => s = σ ∧ FnBase 14 12 insK a σ ∧ BodyIn (geo 12 a) v s) keyBody
    (LiftB (PubF 14) fun a σ _ t => FnBase 14 12 insK a σ ∧ ∃ A live c, Stg (geo 12 a) σ A live c t) :=
  (keyBody_ct (Pub := PubF 14) (gf := geo 12) (fun _ _ p => p.geo_eq (by decide))
    (fun a σ => FnBase 14 12 insK a σ)).mono (fun _ _ h => h)
    fun _ _ h => LiftB.mono (fun _ _ _ _ ⟨x, _, _, _, _, _, _, _, _, _, _, _, A, live, ht⟩ =>
      ⟨x, A, live, _, ht⟩) h

theorem ck_contract_ct : ConstantTime isa (Spec.Rsa.checkKeyContract abi 0).pre
    (Spec.Rsa.checkKeyContract abi 0).pub VG.Impl.Rsa.Arm.CheckKey.code := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  have is := ck_pre s hs
  have it := ck_pre t ht
  sig_pub [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hp
  have args : ∀ i < 14, stackArg s i = stackArg t i := fun i hi =>
    match i, hi with
    | 0, _ => a0 | 1, _ => a1 | 2, _ => a2 | 3, _ => a3 | 4, _ => a4 | 5, _ => a5
    | 6, _ => a6 | 7, _ => a7 | 8, _ => a8 | 9, _ => a9 | 10, _ => a10 | 11, _ => a11
    | 12, _ => a12 | 13, _ => a13
    | _ + 14, h => absurd h (by omega)
  rw [code_eq] at e1 e2
  exact (fn_ct (vf := vK) (by decide) (by decide) entry_taint restore_taint (fun σ _ => ck_hv σ)
    (fun _ h => ck_hA h) ck_body_ct s t tr1 tr2 u v ⟨is, it, VG.Proof.Rsa.Arm.CheckCrtKey.pubF_of sp bytes p0 p1 p2 p3 args⟩ e1 e2).1

/-- A 64-byte modulus, one-byte exponents and factors, the working space at
`0x4000`, and the stack arguments at `0x8000`. -/
def ckSatState : State where
  gpr r := match r with
    | .r0 => 0x2000 | .r1 => 64 | .r2 => 0x3000 | .r3 => 1 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x36 else if a = 0x8004 then 1 else if a = 0x8009 then 0x31
    else if a = 0x800C then 1 else if a = 0x8011 then 0x32 else if a = 0x8014 then 1
    else if a = 0x8019 then 0x33 else if a = 0x801C then 1 else if a = 0x8021 then 0x34
    else if a = 0x8024 then 1 else if a = 0x8029 then 0x35 else if a = 0x802C then 1
    else if a = 0x8031 then 0x40 else if a = 0x8034 then 0x20 else if a = 0x8035 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3600, 1⟩, ⟨0x3100, 1⟩, ⟨0x3200, 1⟩, ⟨0x3300, 1⟩, ⟨0x3400, 1⟩,
    ⟨0x3500, 1⟩, ⟨0x8000, 56⟩]
  wr := [⟨0x4000, 8448⟩]

theorem ck_contract_sat : ∃ s, (Spec.Rsa.checkKeyContract abi 0).pre s := by
  sig_implies_sat [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr]
    [ckSatState, stackArg, stackArgAddr, Mem.readW, Mem.read, Spec.Rsa.lenValid, Spec.Rsa.scratchWords]
    using ckSatState

/-- `vg_rsa_check_key`. -/
theorem check_key_verified :
    Verified target VG.Impl.Rsa.Arm.CheckKey.code (Spec.Rsa.checkKeyContract abi 0) :=
  ⟨ck_contract_correct, ck_contract_ct, ck_contract_sat⟩

end VG.Proof.Rsa.Arm.CheckKey
