module

public import VerifiedGarbage.Impl.Rsa.Arm.InverseCall
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Rsa.Arm.InverseCall
meta import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # A call of `inverse` on ARMv7 (`inverseCall`)

`inverseCall_ok`: what `InvLaw.inverseK_ok` states of `inverse`, for the call
of `inverseFn`, which also writes the header word `sT` (its return
address). `inverseCall_ct`: its addresses and branches depend only on
`r7`–`r9`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Inv
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str)

/-- The header words a call of `inverse` may write. -/
abbrev invCallSlots : List Nat := [sOdd, sB, sC, sT]

/-- A call of code that returns with the `lr` it was called with. -/
theorem WP.call_lrKept {n : String} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s.callEntry fun t => t.gpr .lr = s.callEntry.gpr .lr ∧ Q t) : WP isa (.call n c) s Q := by
  obtain ⟨t, s', he, hl, hq⟩ := h
  refine ⟨_, s', .call (call_callEntry s) he (by simp only [isa, ret, hl, ite_true]), hq⟩

theorem rest_callEntry (s : State) : Rest (.r6 :: opRegs) s s.callEntry := by
  have hsub : ∀ r ∈ linkRegs, r ∈ (.r6 :: opRegs : List Reg) := by decide
  exact ⟨fun r hr => State.callEntry_gpr s fun hl => hr (hsub r hl), rfl, rfl, rfl⟩

theorem inverseCall_ok [InvLaw] {um : Bool} {σ : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk σ B Z W k N)
    (hN15 : 15 ≤ N) (hN : N ≤ 256) (hW8 : 8 ≤ W) :
    WP isa (inverseCall um) σ fun t => Gk t B Z W k N ∧ Keep B W invArrs invCallSlots σ.mem t.mem ∧
      Rest (.r6 :: opRegs) σ t ∧
      (nk σ.mem B W aM k % 2 = 1 → 1 < nk σ.mem B W aM k →
        nk t.mem B W 1 W = Nat.gcd (nk σ.mem B W 0 k) (nk σ.mem B W aM k) ∧
        nk t.mem B W 3 W = VG.Proof.Rsa.Divstep.inv30 k (nk σ.mem B W 0 k) (nk σ.mem B W aM k)) := by
  have hM : aM < N := by have : aM = 8 := rfl; omega_arith
  have h0N : 0 < N := by omega_arith
  have r0 := rest_callEntry σ
  have h0 : Gk σ.callEntry B Z W k N := h.rest r0
  have hz : sT + 4 ≤ Z := by have := h.fits; simp only [arr, hdr, sT] at this ⊢; omega_arith
  have hz1 : sT < Z := Nat.lt_of_lt_of_le (by decide) hz
  have ha : State.addr (σ.callEntry.gpr .r8 + BitVec.ofNat 32 sT) = off (State.addr B) sT := by
    rw [h0.r8]; exact h0.addr hz1
  refine WP.call_lrKept ?_
  simp only [inverseFn]
  rw [WP.seq_iff]
  refine wp_str (by decide) ha (h0.write hz) fun s1 m1 => WP.block_nil_iff.mpr ?_
  have h1 : Gk s1 B Z W k N := h0.rest (ws := []) (m1.rest [])
  have k01 : Keep B W [] [sT] σ.mem s1.mem := by
    rw [m1.mem, State.callEntry_mem]; exact keep_write _ _ (by decide) (by decide)
  have e1 : ∀ j < N, nk s1.mem B W j k = nk σ.mem B W j k := fun j hj =>
    Keep.nk k01 (by have := h.kle; omega_arith) (by simp) (by decide) (h.fit64 hj)
  rw [WP.seq_iff]
  refine WP.mono (InvLaw.inverseK_ok (um := um) h1 hN15 hN hW8) fun t1 ⟨g1, k1, r1, v1⟩ => ?_
  have hb : State.addr (t1.gpr .r8 + BitVec.ofNat 32 sT) = off (State.addr B) sT := by
    rw [g1.r8]; exact g1.addr hz1
  refine wp_ldr (by decide) hb (g1.read hz) fun t2 u2 => WP.block_nil_iff.mpr ?_
  have g2 : Gk t2 B Z W k N := g1.rest (u2.rest (ws := [.lr]) (by simp))
  have sl : slot t1.mem B sT = slot s1.mem B sT := Keep.slot k1 (by decide) (by decide)
  refine ⟨?_, g2, ?_, ?_, fun hmo hm1 => ?_⟩
  · rw [u2.gpr]
    refine BitVec.eq_of_toNat_eq ?_
    have e := sl
    rw [m1.mem, slot_write_self] at e
    exact e
  · rw [u2.mem]
    exact Keep.trans (Keep.mono k01 (by simp) (by decide)) (Keep.mono k1 (by simp) (by decide))
  · exact r0.trans ((m1.rest _).trans (r1.trans (u2.rest (by decide))))
  · rw [← e1 aM hM] at hmo hm1
    obtain ⟨v1a, v1b⟩ := v1 hmo hm1
    rw [u2.mem, v1a, v1b, e1 0 h0N, e1 aM hM]
    exact ⟨rfl, rfl⟩

theorem inverseFn_ct {um : Bool} : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9) (inverseFn um) := by
  have agree : ∀ s t : State, True → True → s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9 →
      taint.Agree (Taint.ofRegs [.r7, .r8, .r9]) s t := by
    intro s t _ _ ⟨h7, h8, h9⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h7
    · exact h8
    · exact h9
  cases um
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r7, .r8, .r9]) agree (by taint_decide)
  · exact VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r7, .r8, .r9]) agree (by taint_decide)

/-- A call of code whose runs from the states it is called in are constant time. -/
theorem RelCT.call_of {n : String} {c : Prog isa} {P P' : State → State → Prop}
    (ct : RelCT isa P' c (fun _ _ => True)) (hp : ∀ s t, P s t → P' s.callEntry t.callEntry) :
    RelCT isa P (.call n c) (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  cases e1 with
  | call p1 b1 q1 =>
    cases e2 with
    | call p2 b2 q2 =>
      rw [call_callEntry, Option.some.injEq] at p1 p2
      subst p1 p2
      obtain ⟨trace, _⟩ := ct _ _ _ _ _ _ (hp _ _ h) b1 b2
      exact ⟨by simpa only [isa, List.map_nil, List.nil_append, List.append_nil] using trace, trivial⟩

/-- A call of `inverseFn`, from states with the same `r7`–`r9`. -/
theorem inverseCall_ct {um : Bool} {P : State → State → Prop}
    (hp : ∀ s t, P s t → s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9) :
    RelCT isa P (inverseCall um) (fun _ _ => True) :=
  RelCT.call_of (P' := fun s t => s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9)
    (fun _ _ _ _ _ _ h e1 e2 => ⟨inverseFn_ct _ _ _ _ _ _ trivial trivial h e1 e2, trivial⟩)
    fun s t h => by
      obtain ⟨h7, h8, h9⟩ := hp _ _ h
      rw [State.callEntry_gpr s (by decide), State.callEntry_gpr t (by decide), State.callEntry_gpr s (by decide),
        State.callEntry_gpr t (by decide), State.callEntry_gpr s (by decide), State.callEntry_gpr t (by decide)]
      exact ⟨h7, h8, h9⟩

end VG.Proof.Rsa.Arm.Keys
