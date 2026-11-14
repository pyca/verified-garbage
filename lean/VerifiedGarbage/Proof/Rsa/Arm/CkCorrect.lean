module

public import VerifiedGarbage.Proof.Rsa.Arm.KcPost
public import VerifiedGarbage.Proof.Rsa.Arm.KcBodyW
import VerifiedGarbage.Proof.Rsa.Arm.KcShape
import VerifiedGarbage.Proof.Rsa.KeyCheckWords
public import VerifiedGarbage.Impl.Rsa.Arm.CheckKey
public import VerifiedGarbage.Proof.Rsa.Arm.KcFn
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Framework.Sig

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

theorem code_eq : VG.Impl.Rsa.Arm.CheckKey.code = fn (4 * 12) (insK.map fun p => (4 * p.1, p.2)) (keyBodyS 12 20 28 36) := rfl

theorem ck_pre (s : State) (h : (Spec.Rsa.checkKeyContract abi 0).pre s) : FnPre 14 12 insK s := by
  sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, abi, argRegs, reduceClassify, Loc.val,
    State.addr] at h
  obtain ⟨sp, rd, wr, dN, dE, dD, dP, dQ, dDP, dDQ, dQI, dA, fN, fE, fD, fP, fQ, fDP, fDQ, fQI, fS, v, e1, e2,
    d1, d2, p1, p2, q1, q2, l1, l2, l3, scr⟩ := h
  refine ⟨by omega_using [sp], by rw [rd]; simp [State.addr], by rw [rd]; simp [State.addr],
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
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [fK, Nat.reduceAdd] <;> omega_arith

/-- The numbers. -/
abbrev vK (σ : State) : Vals := ⟨nV σ, eV σ, inV σ 2, inV σ 4, inV σ 6, inV σ 8, inV σ 10, inV σ 0⟩

theorem ck_hv (σ : State) : aEnt insK σ = vals (vK σ) := rfl

theorem ck_hA {σ : State} (pre : FnPre 14 12 insK σ) : ∀ j < nArr, aEnt insK σ j < 2 ^ (32 * (geo 12 σ).w) := by
  have kb := pre.kb
  have hw : fK σ ≤ 4 * (geo 12 σ).w := by simp only [Geo.w]; omega_using []
  have ins := fun p (hp : p ∈ insK) => (pre.ins1 p hp).2
  have i0 : (stackArg σ 1).toNat ≤ fK σ := ins (0, aD) (by simp)
  have i2 : (stackArg σ 3).toNat ≤ fK σ := ins (2, aP) (by simp)
  have i4 : (stackArg σ 5).toNat ≤ fK σ := ins (4, aQ) (by simp)
  have i6 : (stackArg σ 7).toNat ≤ fK σ := ins (6, aDP) (by simp)
  have i8 : (stackArg σ 9).toNat ≤ fK σ := ins (8, aDQ) (by simp)
  have i10 : (stackArg σ 11).toNat ≤ fK σ := ins (10, aQI) (by simp)
  intro j hj
  rw [ck_hv σ]
  exact vals_lt (Nat.two_pow_pos _) (bytesV_lt (by omega_using [hw])) (bytesV_lt (by have := pre.e2; omega_using [hw, this]))
    (bytesV_lt (k := (stackArg σ 3).toNat) (by omega_using [hw, i2])) (bytesV_lt (k := (stackArg σ 5).toNat) (by omega_using [hw, i4]))
    (bytesV_lt (k := (stackArg σ 7).toNat) (by omega_using [hw, i6])) (bytesV_lt (k := (stackArg σ 9).toNat) (by omega_using [hw, i8]))
    (bytesV_lt (k := (stackArg σ 11).toNat) (by omega_using [hw, i10])) (bytesV_lt (k := (stackArg σ 1).toNat) (by omega_using [hw, i0])) j

/-- `BodyIn` after code that changes only `r0`–`r3` and the flags. -/
theorem _root_.VG.Proof.Rsa.Arm.KeyCheck.BodyIn.of_rest {g : Geo} {v : Vals} {s t : State} (h : BodyIn g v s) (r : Rest [.r0, .r1, .r2, .r3] s t)
    (m : t.mem = s.mem) : BodyIn g v t :=
  ⟨h.nowrap, r.wr ▸ h.writable, h.fits, h.kb, (r.gpr _ (by decide)).trans h.r8, (r.gpr _ (by decide)).trans h.r11,
    m ▸ h.cnt, m ▸ h.arrs, m ▸ h.vdTop⟩

/-- `Stg` from before code that changes only `r0`–`r3` and the flags. -/
theorem _root_.VG.Proof.Rsa.Arm.KeyCheck.Stg.of_pre {g : Geo} {s t u : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
    (h : Stg g t A live c u) (r : Rest [.r0, .r1, .r2, .r3] s t) (m : t.mem = s.mem) : Stg g s A live c u :=
  ⟨h.ws, m ▸ h.keep, (r.mono fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide).trans h.rest,
    h.cnt, h.arrs, h.live_lt, h.vdTop, h.mask⟩

/-- `keyBodyS`: the balanced key's checks or the others; either way the mask is `keyP`'s. -/
theorem keyBodyS_post {σ s : State} (m : Mid 14 12 insK σ s (aEnt insK σ)) (bi : BodyIn (geo 12 σ) (vK σ) s)
    (hm : Spec.Rsa.modulusValid (nV σ) (fK σ) = true) (hev : Spec.Rsa.exponentValid (eV σ) = true)
    (l2 : (stackArg σ 11).toNat = (stackArg σ 3).toNat) :
    WP isa (keyBodyS 12 20 28 36) s fun t => ∃ A live c, Stg (geo 12 σ) s A live c t ∧ keyP (geo 12 σ) (vK σ) c := by
  have pre := m.base.pre
  have kb := pre.kb
  have e33 : eV σ < 2 ^ 33 := by
    simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hev; exact hev.2
  unfold keyBodyS
  rw [WP.seq_iff]
  refine shape_ok m.base m.r11 (by decide) fun t bt rt mt zt => ?_
  have bi' := bi.of_rest rt mt
  refine WP.ite t.z rfl (fun hz => ?_) (fun _ => ?_)
  · rw [zt] at hz
    obtain ⟨lp, lq, ld, le, he⟩ := of_decide_eq_true hz
    have hpw : (stackArg σ 3).toNat ≤ 4 * ((geo 12 σ).w / 2) := by omega_using [lp, he]
    have hqw : (stackArg σ 5).toNat ≤ 4 * ((geo 12 σ).w / 2) := by omega_using [lq, he]
    have hdw : (stackArg σ 7).toNat ≤ 4 * ((geo 12 σ).w / 2) := by omega_using [ld, he]
    have hew : (stackArg σ 9).toNat ≤ 4 * ((geo 12 σ).w / 2) := by omega_using [le, he]
    refine WP.mono (keyBodyW_ok bi' he (bytesV_lt hpw) (bytesV_lt hqw) (bytesV_lt hdw) (bytesV_lt hew)
        (bytesV_lt (k := (stackArg σ 11).toNat) (by rw [l2]; exact hpw)) (Nat.lt_of_lt_of_le e33 (by decide)))
      fun u ⟨A, live, hu⟩ => ⟨A, live, _, hu.of_pre rt mt, _, _, _, _, _, _, _, fun _ => ⟨rfl, rfl⟩,
        ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun _ => rfl, fun _ => rfl,
        VG.Proof.Rsa.keyBits_words2 hm rfl (by simp only [Geo.w]; omega_using [kb]) he (bytesV_lt hpw) (bytesV_lt hqw)
          (bytesV_lt hdw) (bytesV_lt hew) e33⟩
  · exact WP.mono (keyBody_post bi') fun u ⟨A, live, c, hu, hk⟩ => ⟨A, live, c, hu.of_pre rt mt, hk⟩

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
  refine WP.mono (fn_ok pre (by decide) (ck_hv σ) (ck_hA pre) fun s m hs hm he => keyBodyS_post m hs hm he l2)
    fun u ⟨pres, c, hc, hr⟩ => ⟨pres, ?_⟩
  rw [hr, key_result (g := geo 12 σ) (VG.Proof.Rsa.Arm.CrtValues.bytesAt_length _ _ _)
    (by show 0 < fK σ; omega_using [hp]) (by rw [VG.Proof.Rsa.Arm.CrtValues.bytesAt_length]; exact hp)
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
