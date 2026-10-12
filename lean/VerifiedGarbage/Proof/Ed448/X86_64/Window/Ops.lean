import VerifiedGarbage.Proof.Ed448.X86_64.Window.Memory
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall

/-! Point operations and coordinate transfers used by the verification windows. -/
namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk)

/-- Copy the addition result, preserving every other coordinate. -/
theorem accept_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block accept) s fun u => Keep base s u ∧
      pt (E u.mem base) 0 1 2 = pt (E s.mem base) 3 4 5 ∧
      ∀ j : Index, 3 ≤ j.val → E u.mem base j = E s.mem base j := by
  rw [accept, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copySlot_ok hs 0 3) fun s1 ⟨k1, e1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copySlot_ok (k1.scr hs) 1 4) fun s2 ⟨k2, e2⟩ => ?_
  refine WP.mono (copySlot_ok (k2.scr (k1.scr hs)) 2 5) fun u ⟨ku, eu⟩ => ?_
  refine ⟨(k1.trans k2).trans ku, ?_, ?_⟩
  · rw [eu, e2, e1]; rfl
  · intro j hj
    have h0 : j ≠ 0 := by intro h; subst j; contradiction
    have h1 : j ≠ 1 := by intro h; subst j; contradiction
    have h2 : j ≠ 2 := by intro h; subst j; contradiction
    rw [eu, e2, e1, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]

/-- Projective addition with the existing specialized multiplication by `d`. -/
theorem add_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F) {s : State} {base : Addr}
    (hs : Scr s base) (hd : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (Window.add F) s fun u => Keep base s u ∧ E u.mem base = evalOps addOps (E s.mem base) := by
  rw [Window.add, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf (addOps.take 4) (by decide) hs) fun s1 ⟨k1, e1⟩ => ?_
  rw [WP.block_append_iff]
  have d1 : E s1.mem base 11 = Spec.Ed448.d := by rw [e1]; exact hd
  refine WP.mono (Point64.mulD_ok (k1.scr hs) d1) fun s2 ⟨k2, e2, _⟩ => ?_
  refine WP.mono (fieldCode_ok hf (addOps.drop 5) (by decide) (k2.scr (k1.scr hs))) fun u ⟨ku, eu⟩ => ?_
  refine ⟨(k1.trans k2).trans ku, ?_⟩
  rw [eu, e2, e1]
  conv => rhs; rw [show addOps = addOps.take 4 ++ [.mul 16 11 14] ++ addOps.drop 5 from rfl]
  simp only [evalOps, List.foldl_append, List.foldl_cons, List.foldl_nil]

def dbl4Pt (p : Spec.Ed448.Point) := double (double (double (double p)))

theorem dbl4_ok {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (dbl4 P) s fun u => Keep base s u ∧
      pt (E u.mem base) 0 1 2 = dbl4Pt (pt (E s.mem base) 0 1 2) ∧
      ∀ j : Index, 3 ≤ j.val → j.val < 12 → E u.mem base j = E s.mem base j := by
  rw [dbl4]
  refine WP.seq (WP.mono (hP.dbl hs) fun s1 ⟨k1, e1⟩ => ?_)
  refine WP.seq (WP.mono (hP.dbl (k1.scr hs)) fun s2 ⟨k2, e2⟩ => ?_)
  refine WP.seq (WP.mono (hP.dbl (k2.scr (k1.scr hs))) fun s3 ⟨k3, e3⟩ => ?_)
  refine WP.mono (hP.dbl (k3.scr (k2.scr (k1.scr hs)))) fun u ⟨ku, eu⟩ => ?_
  refine ⟨((k1.trans k2).trans k3).trans ku, ?_, ?_⟩
  · rw [eu, doubleOps_eval, e3, doubleOps_eval, e2, doubleOps_eval, e1, doubleOps_eval]; rfl
  · intro j hj hj'
    rw [eu, doubleOps_keep _ _ (Or.inl ⟨hj, hj'⟩), e3, doubleOps_keep _ _ (Or.inl ⟨hj, hj'⟩),
      e2, doubleOps_keep _ _ (Or.inl ⟨hj, hj'⟩), e1, doubleOps_keep _ _ (Or.inl ⟨hj, hj'⟩)]

theorem dbl4Pt_rep {p : Spec.Ed448.Point} {a : EdwardsLaw.EPoint dZ} (h : Rep p a) :
    Rep (dbl4Pt p) ((16 : Nat) • a) := by
  have h4 := double_rep (double_rep (double_rep (double_rep h)))
  simpa only [dbl4Pt, ← two_nsmul, smul_smul, Nat.reduceMul] using h4

end VG.Proof.Ed448.X86_64.Window
