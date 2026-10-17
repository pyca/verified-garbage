module

public import VerifiedGarbage.Proof.Rsa.Arm.KcPost
public import VerifiedGarbage.Impl.Rsa.Arm.CheckKey
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_check_key` on ARMv7: correctness

`ck_pre`: the contract's precondition as `FnPre`; `ck_ok`: the code returns
with the callee-saved registers and `sp` restored and `checkKey` of the key
in `r0`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CheckKey
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.KeyCheck
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.CrtValues (reg)

/-- The numbers on the stack: their pointers' words and arrays. -/
abbrev insK : List (Nat × Nat) := [(0, aD), (2, aP), (4, aQ), (6, aDP), (8, aDQ), (10, aQI)]

theorem code_eq : VG.Impl.Rsa.Arm.CheckKey.code = fn (4 * 12) (insK.map fun p => (4 * p.1, p.2)) keyBody := rfl

theorem ck_pre (s : State) (h : (Spec.Rsa.checkKeyContract abi 0).pre s) : FnPre 14 12 insK s := by
  sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at h
  obtain ⟨sp, rd, wr, dN, dE, dD, dP, dQ, dDP, dDQ, dQI, dA, fN, fE, fD, fP, fQ, fDP, fDQ, fQI, fS, v, e1, e2,
    d1, d2, p1, p2, q1, q2, l1, l2, l3, scr⟩ := h
  refine ⟨by omega, by rw [rd]; simp [State.addr], by rw [rd]; simp [State.addr],
    by rw [rd]; simp [stackArgAddr], fun p hp => ?_, by rw [wr]; rfl, dN, dE, fun p hp => ?_, dA, fN, fE,
    fun p hp => ?_, fS, v, e1, e2, fun p hp => ?_, scr, by decide, by decide, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [rd] <;> simp [State.addr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [dD, dP, dQ, dDP, dDQ, dQI]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [fD, fP, fQ, fDP, fDQ, fQI]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [fK, Nat.reduceAdd] <;> omega

/-- The numbers. -/
abbrev vK (σ : State) : Vals := ⟨nV σ, eV σ, inV σ 2, inV σ 4, inV σ 6, inV σ 8, inV σ 10, inV σ 0⟩

theorem ck_hv (σ : State) : aEnt insK σ = vals (vK σ) := rfl

theorem ck_hA {σ : State} (pre : FnPre 14 12 insK σ) : ∀ j < nArr, aEnt insK σ j < 2 ^ (32 * (geo 12 σ).w) := by
  have kb := pre.kb
  have hw : fK σ ≤ 4 * (geo 12 σ).w := by simp only [Geo.w]; omega
  have ins := fun p (hp : p ∈ insK) => (pre.ins1 p hp).2
  have i0 : (stackArg σ 1).toNat ≤ fK σ := ins (0, aD) (by simp)
  have i2 : (stackArg σ 3).toNat ≤ fK σ := ins (2, aP) (by simp)
  have i4 : (stackArg σ 5).toNat ≤ fK σ := ins (4, aQ) (by simp)
  have i6 : (stackArg σ 7).toNat ≤ fK σ := ins (6, aDP) (by simp)
  have i8 : (stackArg σ 9).toNat ≤ fK σ := ins (8, aDQ) (by simp)
  have i10 : (stackArg σ 11).toNat ≤ fK σ := ins (10, aQI) (by simp)
  intro j hj
  rw [ck_hv σ]
  exact vals_lt (Nat.two_pow_pos _) (bytesV_lt (by omega)) (bytesV_lt (by have := pre.e2; omega))
    (bytesV_lt (k := (stackArg σ 3).toNat) (by omega)) (bytesV_lt (k := (stackArg σ 5).toNat) (by omega))
    (bytesV_lt (k := (stackArg σ 7).toNat) (by omega)) (bytesV_lt (k := (stackArg σ 9).toNat) (by omega))
    (bytesV_lt (k := (stackArg σ 11).toNat) (by omega)) (bytesV_lt (k := (stackArg σ 1).toNat) (by omega)) j

theorem ck_ok {σ : State} (pre : FnPre 14 12 insK σ) (l1 : (stackArg σ 7).toNat = (stackArg σ 3).toNat)
    (l2 : (stackArg σ 11).toNat = (stackArg σ 3).toNat) (l3 : (stackArg σ 9).toNat = (stackArg σ 5).toNat)
    (hp : (stackArg σ 3).toNat < fK σ) (hq : (stackArg σ 5).toNat < fK σ) :
    WP isa VG.Impl.Rsa.Arm.CheckKey.code σ fun u => abiPreserved σ u ∧
      u.gpr .r0 = if Spec.Rsa.checkKey
          (Spec.Rsa.bytesAt σ.mem (State.addr (σ.gpr .r0)) (σ.gpr .r1).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (σ.gpr .r2)) (σ.gpr .r3).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 0)) (stackArg σ 1).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 2)) (stackArg σ 3).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 4)) (stackArg σ 5).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 6)) (stackArg σ 3).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 8)) (stackArg σ 5).toNat)
          (Spec.Rsa.bytesAt σ.mem (State.addr (stackArg σ 10)) (stackArg σ 3).toNat) then 1 else 0 := by
  have kb := pre.kb
  rw [code_eq]
  refine WP.mono (fn_ok pre (by decide) (ck_hv σ) (ck_hA pre) fun s hs => keyBody_post hs)
    fun u ⟨pres, c, hc, hr⟩ => ⟨pres, ?_⟩
  rw [hr, key_result (g := geo 12 σ) (VG.Proof.Rsa.Arm.CrtValues.bytesAt_length _ _ _)
    (by show 0 < fK σ; omega) (by rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; exact hp)
    (by rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; exact hq) hc]
  rw [show (0 + 1 : Nat) = 1 from rfl, show (2 + 1 : Nat) = 3 from rfl, show (4 + 1 : Nat) = 5 from rfl,
    show (6 + 1 : Nat) = 7 from rfl, show (8 + 1 : Nat) = 9 from rfl, show (10 + 1 : Nat) = 11 from rfl,
    l1, l2, l3, show (geo 12 σ).K = (σ.gpr .r1).toNat from rfl]
  split <;> rfl

theorem ck_contract_correct (s : State) (h : (Spec.Rsa.checkKeyContract abi 0).pre s) :
    ∃ tr t, Exec isa VG.Impl.Rsa.Arm.CheckKey.code s tr t ∧ abiPreserved s t ∧
      (Spec.Rsa.checkKeyContract abi 0).post s t := by
  have pre := ck_pre s h
  sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p2, -, q2, l1, l2,
    l3, -⟩ := h
  obtain ⟨tr, t, run, pres, r0⟩ := ck_ok pre l1 l2 l3 p2 q2
  refine ⟨tr, t, run, pres, ?_⟩
  sig_post [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact r0

end VG.Proof.Rsa.Arm.CheckKey
