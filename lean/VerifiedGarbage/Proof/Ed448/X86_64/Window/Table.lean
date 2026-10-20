module
public import VerifiedGarbage.Proof.Ed448.Window
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
public import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory

import VerifiedGarbage.Proof.Ed448.X86_64.Window.Ops
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Build all seventeen projective multiples without inversions. Invalid decoded points
still execute safely; group membership is needed only when interpreting the final equation. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr E Keep Index)
open VG.Proof.Ed448.Window (multiples)

private theorem build_ok {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) (hd : E s.mem base 11 = Spec.Ed448.d) {A : Spec.Ed448.Point} (hAz : A.Z = 1)
    (hA : pt (E s.mem base) 8 9 10 = A) (hp : pt (E s.mem base) 0 1 2 = Spec.Ed448.identity)
    (h0 : tablePoint s.mem base 0 = Spec.Ed448.identity) (n : Nat) (hn : n < 17) :
    WP isa (build P n) s fun u => KeepW base s u ∧ E u.mem base 11 = Spec.Ed448.d ∧
      pt (E u.mem base) 8 9 10 = A ∧ pt (E u.mem base) 0 1 2 = multiples A n ∧
      ∀ i ≤ n, tablePoint u.mem base i = multiples A i := by
  induction n with
  | zero =>
    refine WP.block_nil ⟨KeepW.refl _ _, hd, hA, hp, fun i hi => ?_⟩
    have he : i = 0 := by omega
    subst i
    exact h0
  | succ n ih =>
    rw [build]
    refine WP.seq (WP.mono (ih (by omega)) fun s1 ⟨k1, d1, a1, p1, t1⟩ => ?_)
    refine WP.seq (WP.mono (hP.add (k1.scr hs) d1) fun s2 ⟨k2, e2⟩ => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (accept_ok (k2.scr (k1.scr hs))) fun s3 ⟨k3, p3, f3⟩ => ?_
    refine WP.mono (store_ok (k3.scr (k2.scr (k1.scr hs))) (n + 1) hn) fun u ⟨ku, ou, eu, pu⟩ => ?_
    have p3' : pt (E s3.mem base) 0 1 2 = multiples A (n + 1) := by
      have hz : E s1.mem base 10 = 1 := (congrArg Spec.Ed448.Point.Z a1).trans hAz
      have qa : (⟨E s1.mem base 8, E s1.mem base 9, 1⟩ : Spec.Ed448.Point) = A := by
        rw [← hz]; exact a1
      rw [p3, e2, Point64.addAffineOps_eval, d1, addWith_d, qa, p1]; rfl
    refine ⟨((k1.trans (KeepW.of_keep k2)).trans (KeepW.of_keep k3)).trans ku, ?_, ?_, ?_, ?_⟩
    · rw [eu, f3 11 (by decide), e2, Point64.addAffineOps_keep _ _ (Or.inr (Or.inl (by decide))), d1]
    · rw [eu, pt_congr (f3 8 (by decide)) (f3 9 (by decide)) (f3 10 (by decide)), e2]
      rw [pt_congr (Point64.addAffineOps_keep _ _ (Or.inr (Or.inl (by decide))))
        (Point64.addAffineOps_keep _ _ (Or.inr (Or.inl (by decide))))
        (Point64.addAffineOps_keep _ _ (Or.inr (Or.inl (by decide))))]
      exact a1
    · rw [eu]; exact p3'
    · intro i hi
      by_cases he : i = n + 1
      · subst i; rw [pu]; exact p3'
      · have hi' : i ≤ n := by omega
        rw [show tablePoint u.mem base i = tablePoint s3.mem base i from
          pointAt_outside ou (by simp only [tabOffset, TAB]; omega) (by simp only [tabOffset]; omega),
          tablePoint_keep k3 i (by omega), tablePoint_keep k2 i (by omega)]
        exact t1 i hi'

/-- The precomputed table preserves the scalar bits, saved registers, decoded `R`, and checks. -/
theorem table_ok {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) (hd : E s.mem base 11 = Spec.Ed448.d)
    (hz : E s.mem base 10 = 1) (hp : pt (E s.mem base) 0 1 2 = Spec.Ed448.identity) :
    WP isa (table P) s fun u => KeepW base s u ∧ E u.mem base 11 = Spec.Ed448.d ∧
      ∀ i < 17, tablePoint u.mem base i = multiples (pt (E s.mem base) 6 7 10) i := by
  rw [table]
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (copySlot_ok hs 8 6) fun s1 ⟨k1, e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copySlot_ok (k1.scr hs) 9 7) fun s2 ⟨k2, e2⟩ => ?_
  refine WP.mono (store_ok (k2.scr (k1.scr hs)) 0 (by decide)) fun s3 ⟨k3, _, e3, p3⟩ => ?_
  have ds : E s3.mem base 11 = Spec.Ed448.d := by rw [e3, e2, e1]; exact hd
  have az : (pt (E s.mem base) 6 7 10).Z = 1 := hz
  have aa : pt (E s3.mem base) 8 9 10 = pt (E s.mem base) 6 7 10 := by
    rw [e3, e2, e1]; simp (disch := decide) only [pt, Function.update_self, Function.update_of_ne]
  have pp : pt (E s3.mem base) 0 1 2 = Spec.Ed448.identity := by
    rw [e3, e2, e1, ← hp]; simp (disch := decide) only [pt, Function.update_of_ne]
  have tt : tablePoint s3.mem base 0 = Spec.Ed448.identity := by
    rw [p3, e2, e1, ← hp]; simp (disch := decide) only [pt, Function.update_of_ne]
  refine WP.mono (build_ok hP (k3.scr (k2.scr (k1.scr hs))) ds az aa pp tt 16 (by decide))
    fun u ⟨ku, du, _, _, tu⟩ => ?_
  exact ⟨((KeepW.of_keep (k1.trans k2)).trans k3).trans ku, du, fun i hi => tu i (by omega)⟩

end VG.Proof.Ed448.X86_64.Window
