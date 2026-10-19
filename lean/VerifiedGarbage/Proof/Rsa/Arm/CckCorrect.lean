module

import VerifiedGarbage.Proof.Rsa.Arm.KcPost
public import VerifiedGarbage.Impl.Rsa.Arm.CheckCrtKey
public import VerifiedGarbage.Proof.Rsa.Arm.KcFn
import VerifiedGarbage.Proof.Rsa.Arm.CvFail

/-! # `vg_rsa_check_crt_key` on ARMv7: correctness

`cck_pre`: the contract's precondition as `FnPre`; `cck_ok`: the code returns
with the callee-saved registers and `sp` restored and `checkCrtKey` of the
key in `r0`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CheckCrtKey
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.KeyCheck
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.CrtValues (reg)

/-- The numbers on the stack: their pointers' words and arrays. -/
abbrev insC : List (Nat × Nat) := [(0, aP), (2, aQ), (4, aDP), (6, aDQ), (8, aQI)]

theorem code_eq : VG.Impl.Rsa.Arm.CheckCrtKey.code = fn (4 * 10) (insC.map fun p => (4 * p.1, p.2)) crtBody := rfl

theorem cck_pre (s : State) (h : (Spec.Rsa.checkCrtKeyContract abi 0).pre s) : FnPre 12 10 insC s := by
  sig_pre [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at h
  obtain ⟨sp, rd, wr, dN, dE, dP, dQ, dDP, dDQ, dQI, dA, fN, fE, fP, fQ, fDP, fDQ, fQI, fS, v, e1, e2, p1, p2,
    q1, q2, l1, l2, l3, scr⟩ := h
  refine ⟨by omega, by rw [rd]; simp [reg, State.addr], by rw [rd]; simp [reg, State.addr],
    by rw [rd]; simp [stackArgAddr], fun p hp => ?_, by rw [wr]; rfl, dN, dE, fun p hp => ?_, dA, fN, fE,
    fun p hp => ?_, fS, v, e1, e2, fun p hp => ?_, scr, by decide, by decide, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> rw [rd] <;> simp [State.addr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [dP, dQ, dDP, dDQ, dQI]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    exacts [fP, fQ, fDP, fDQ, fQI]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp only [fK, Nat.reduceAdd] <;> omega

/-- The numbers. -/
abbrev vC (σ : State) : Vals := ⟨nV σ, eV σ, inV σ 0, inV σ 2, inV σ 4, inV σ 6, inV σ 8, 0⟩

theorem cck_hv (σ : State) : aEnt insC σ = vals (vC σ) := by
  unfold vals
  rw [upd_noop (A := upd (fun _ => 0) aE (vC σ).e) (j := aD) (v := (vC σ).d) rfl]
  rfl

theorem cck_hA {σ : State} (pre : FnPre 12 10 insC σ) : ∀ j < nArr, aEnt insC σ j < 2 ^ (32 * (geo 10 σ).w) := by
  have kb := pre.kb
  have hw : fK σ ≤ 4 * (geo 10 σ).w := by simp only [Geo.w]; omega
  have ins := fun p (hp : p ∈ insC) => (pre.ins1 p hp).2
  have i0 : (stackArg σ 1).toNat ≤ fK σ := ins (0, aP) (by simp)
  have i2 : (stackArg σ 3).toNat ≤ fK σ := ins (2, aQ) (by simp)
  have i4 : (stackArg σ 5).toNat ≤ fK σ := ins (4, aDP) (by simp)
  have i6 : (stackArg σ 7).toNat ≤ fK σ := ins (6, aDQ) (by simp)
  have i8 : (stackArg σ 9).toNat ≤ fK σ := ins (8, aQI) (by simp)
  intro j hj
  rw [cck_hv σ]
  exact vals_lt (Nat.two_pow_pos _) (bytesV_lt (by omega)) (bytesV_lt (by have := pre.e2; omega))
    (bytesV_lt (k := (stackArg σ 1).toNat) (by omega)) (bytesV_lt (k := (stackArg σ 3).toNat) (by omega))
    (bytesV_lt (k := (stackArg σ 5).toNat) (by omega)) (bytesV_lt (k := (stackArg σ 7).toNat) (by omega))
    (bytesV_lt (k := (stackArg σ 9).toNat) (by omega)) (Nat.two_pow_pos _) j

theorem cck_ok {σ : State} (pre : FnPre 12 10 insC σ) (l1 : (stackArg σ 5).toNat = (stackArg σ 1).toNat)
    (l2 : (stackArg σ 9).toNat = (stackArg σ 1).toNat) (l3 : (stackArg σ 7).toNat = (stackArg σ 3).toNat)
    (hp : (stackArg σ 1).toNat < fK σ) (hq : (stackArg σ 3).toNat < fK σ) :
    WP isa VG.Impl.Rsa.Arm.CheckCrtKey.code σ fun u => abiPreserved σ u ∧
      u.gpr .r0 = if Spec.Rsa.checkCrtKey
          (Spec.Rsa.bytesAt σ.mem (State.addr (σ.gpr .r0)) (σ.gpr .r1).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (σ.gpr .r2)) (σ.gpr .r3).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 0)) (stackArg σ 1).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 2)) (stackArg σ 3).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 4)) (stackArg σ 1).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 6)) (stackArg σ 3).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 8)) (stackArg σ 1).toNat) then 1 else 0 := by
  have kb := pre.kb
  rw [code_eq]
  refine WP.mono (fn_ok pre (by decide) (cck_hv σ) (cck_hA pre) fun s hs => crtBody_post hs)
    fun u ⟨pres, c, hc, hr⟩ => ⟨pres, ?_⟩
  rw [hr, crt_result (g := geo 10 σ) (VG.Proof.Rsa.Arm.CrtValues.bytesAt_length _ _ _)
    (by show 0 < fK σ; omega) (by rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; exact hp)
    (by rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; exact hq) hc]
  rw [show (2 + 1 : Nat) = 3 from rfl, show (4 + 1 : Nat) = 5 from rfl, show (6 + 1 : Nat) = 7 from rfl,
    show (8 + 1 : Nat) = 9 from rfl, l1, l2, l3, show (geo 10 σ).K = (σ.gpr .r1).toNat from rfl]
  split <;> rfl

end VG.Proof.Rsa.Arm.CheckCrtKey

namespace VG.Proof.Rsa.Arm.CheckCrtKey
open VG VG.Arm VG.Proof.Rsa.Arm.KeyCheck

theorem cck_contract_correct (s : State) (h : (Spec.Rsa.checkCrtKeyContract abi 0).pre s) :
    ∃ tr t, Exec isa VG.Impl.Rsa.Arm.CheckCrtKey.code s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.checkCrtKeyContract abi 0).post s t := by
  have pre := cck_pre s h
  sig_pre [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p2, -, q2, l1, l2, l3, -⟩ := h
  obtain ⟨tr, t, run, pres, r0⟩ := cck_ok pre l1 l2 l3 p2 q2
  refine ⟨tr, t, run, pres, ?_⟩
  sig_post [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact r0

end VG.Proof.Rsa.Arm.CheckCrtKey
