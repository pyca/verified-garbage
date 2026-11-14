module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KcBase

import VerifiedGarbage.Proof.Rsa.X86.KcWord
import VerifiedGarbage.Proof.Rsa.X86.KcOps
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Framework.Block

/-! # Initial state for i686 RSA key validation -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck VG.Impl.Rsa.X86.KeyCheckRt
open VG.Proof.Rsa.X86.Keys

structure BodyIn (g : Geo) (v : Vals) (s : State) : Prop where
  ws : VG.Proof.Rsa.X86.KeyRt.RtWs g.L s g.B g.Z g.len nArr
  arrs : Arrs s.mem g.B g.w (vals v) (List.range nArr)
  vdTop : w32 s.mem g.B (arr g.w aVD + 4 * g.w) = 0
  /-- `q`'s length argument, whose bytes bound `q`. -/
  qLen : ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ v.q < 2 ^ (8 * a) ∧
    VG.Proof.Bignum.X86.CallArgument s g.B g.Z (qLenArg g.full) (BitVec.ofNat 32 a)
  /-- `p`'s. -/
  pLen : ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ v.p < 2 ^ (8 * a) ∧
    VG.Proof.Bignum.X86.CallArgument s g.B g.Z (pLenArg g.full) (BitVec.ofNat 32 a)

abbrev live0 : List Nat := [aZ, aOne, aN, aE, aP, aQ, aDP, aDQ, aQI, aD]

theorem first_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa (.seq (.block (VG.Impl.Rsa.X86.KeyRt.setOne g.L aOne)) (.block (VG.Impl.Rsa.X86.KeyRt.bitOf g.L sMask aP))) s
      (Stg g s (upd (vals v) aOne 1) live0 (decide (v.p % 2 = 1))) := by
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.setOne_ok h.ws (j := aOne) (by decide)) fun s4 ⟨h4, k4, e4, r4⟩ => ?_
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.bitOf_ok h4 (j := aP) (by decide) (by decide)) fun t ⟨ht, k5, e5, r5⟩ => ?_
  have a3 : Arrs s.mem g.B g.w (vals v) live0 := h.arrs.sub (by decide)
  have a4 : Arrs s4.mem g.B g.w (upd (vals v) aOne 1) live0 := by
    refine a3.write k4 h.ws.ws ?_ (by decide) (by simp)
    rw [e4, a3.get (by decide), show vals v aOne = 0 by rfl]
  have p4 : num s4.mem g.B g.w aP = v.p := by rw [a4.get (by decide)]; rfl
  refine ⟨ht, (k4.mono (by decide) (by simp)).trans (k5.mono (by simp) (by decide)),
    (r4.mono (by decide)).trans (r5.mono (by decide)), a4.keep k5 ht.ws (by decide) (by decide),
    by decide, ?_, ?_⟩
  · rw [k5.word (by unfold S Geo.w; omega_using []) (by simp) (by decide) (h.ws.ws.fit64 (by decide)),
      k4.word (by unfold S Geo.w; omega_using []) (by decide) (by simp) (h.ws.ws.fit64 (by decide)), h.vdTop]
  · rw [e5, p4]
    rcases Nat.mod_two_eq_zero_or_one v.p with e | e <;> simp [e]

/-- The arrays after `start`. -/
abbrev aStart (v : Vals) : Nat → Nat := upd (vals v) aOne 1

/-- `start`: `1`, and the mask of `p` odd and `p q = n`. -/
theorem start_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa (start g.full) s (Stg g s (aStart v) live0 (decide (v.p % 2 = 1) && decide (v.p * v.q = v.n))) := by
  unfold start
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have f := first_ok h
  rw [WP.seq_iff] at f
  refine WP.mono f fun u hu => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono hu fun t ht => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  -- The guard, then the product: over the primes' `w / 2` words where it holds.
  obtain ⟨ap, -, hap, plt, parg⟩ := h.pLen
  obtain ⟨aq, -, haq, qlt, qarg⟩ := h.qLen
  refine WP.mono (ht.balanced_ok (ht.arg parg) (ht.arg qarg) hap haq (by decide))
    fun t7 ⟨h7, an, _, _, hkw, hg⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h7.ifBalanced_ok hg (Q := fun t1 => Stg g s (aStart v) live0 (decide (v.p % 2 = 1)) t1 ∧
      val32 t1.mem g.B (arr g.w aVQ) (2 * g.w) = aStart v aP * aStart v aQ)
    (fun bal u hu => ?_) fun _ u hu => hu.mulWide_ok (o := aVQ) (a := aP) (b := aQ) (by decide) (by decide)
      (by decide) (by decide) (by decide)) fun t1 ⟨h1, e1⟩ => ?_
  · obtain ⟨h8, hpa, hqa, -, -⟩ := bal
    have hkw' : VG.Proof.Rsa.X86.KeyRt.kw an = g.w := hkw
    have hw : g.w = an / 4 := by
      rw [← hkw']
      simp only [VG.Proof.Rsa.X86.KeyRt.kw, Spec.Rsa.modulusWords]; omega_using [h8]
    have e8 : 32 * (g.w / 2) = 8 * ap := by omega_using [h8, hpa, hw]
    exact hu.mulHalf_ok (o := aVQ) (a := aP) (b := aQ) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by show v.p < _; rw [e8]; exact plt) (by show v.q < _; rw [e8, show 8 * ap = 8 * aq by omega_using [hpa, hqa]]; exact qlt)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (h1.eqWide_ok (o := aVQ) (n := aN) (by decide) (by decide)) fun t2 ⟨h2, e2⟩ => ?_
  refine h2.acc_ok ?_
  rw [e2, e1]
  change (if v.p * v.q = v.n then 1 else 0) = _
  by_cases hh : v.p * v.q = v.n <;> simp [hh]
end VG.Proof.Rsa.X86.KeyCheck
