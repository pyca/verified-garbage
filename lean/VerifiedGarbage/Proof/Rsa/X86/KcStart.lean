module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KcBase

import VerifiedGarbage.Proof.Rsa.X86.KcDiv
import VerifiedGarbage.Proof.Rsa.X86.KeyWord
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeyBits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.X86.Wp

/-! # Initial state for i686 RSA key validation -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

structure BodyIn (g : Geo) (v : Vals) (s : State) : Prop where
  ws : Ws s g.B g.Z g.w nArr
  arrs : Arrs s.mem g.B g.w (vals v) (List.range nArr)
  vdTop : w32 s.mem g.B (arr g.w aVD + 4 * g.w) = 0

abbrev live0 : List Nat := [aZ, aOne, aN, aE, aP, aQ, aDP, aDQ, aQI, aD]

theorem first_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa (.seq (.block (setOne g.w aOne)) (.block (bitOf g.w sMask aP))) s
      (Stg g s (upd (vals v) aOne 1) live0 (decide (v.p % 2 = 1))) := by
  rw [WP.seq_iff]
  refine WP.mono (setOne_ok h.ws (j := aOne) (by decide)) fun s4 ⟨h4, k4, e4, r4⟩ => ?_
  refine WP.mono (bitOf_ok h4 (j := aP) (by decide) (by decide)) fun t ⟨ht, k5, e5, r5⟩ => ?_
  have a3 : Arrs s.mem g.B g.w (vals v) live0 := h.arrs.sub (by decide)
  have a4 : Arrs s4.mem g.B g.w (upd (vals v) aOne 1) live0 := by
    refine a3.write k4 h.ws ?_ (by decide) (by simp)
    rw [e4, a3.get (by decide), show vals v aOne = 0 by rfl]
  have p4 : num s4.mem g.B g.w aP = v.p := by rw [a4.get (by decide)]; rfl
  refine ⟨ht, (k4.mono (by decide) (by simp)).trans (k5.mono (by simp) (by decide)),
    (r4.mono (by decide)).trans (r5.mono (by decide)), a4.keep k5 ht (by decide) (by decide),
    by decide, ?_, ?_⟩
  · rw [k5.word (by unfold S; omega) (by simp) (by decide) (h.ws.fit64 (by decide)),
      k4.word (by unfold S; omega) (by decide) (by simp) (h.ws.fit64 (by decide)), h.vdTop]
  · rw [e5, p4]
    rcases Nat.mod_two_eq_zero_or_one v.p with e | e <;> simp [e]

theorem start_ok {g : Geo} {v : Vals} {s : State} (h : BodyIn g v s) :
    WP isa (start g.w) s fun u =>
      WP isa (division g.w) u fun t => ∃ Xq Xr,
        (0 < v.p → Xr = v.n % v.p ∧ Xq = v.n / v.p) ∧
        Stg g s (upd (upd (upd (vals v) aOne 1) aVQ Xq) aVR Xr)
          (aVR :: aVQ :: live0) (decide (v.p % 2 = 1)) t := by
  unfold start
  rw [wp_seqs_append (by simp) (by simp [divSet])]
  exact WP.mono (first_ok h) fun u hu => hu.divSet_ok (a := aN) (d := aP) (by decide) (by decide) (by decide)
end VG.Proof.Rsa.X86.KeyCheck
