module
public import VerifiedGarbage.Impl.Ed448.X86_64.Window
public import VerifiedGarbage.Proof.Ed448.Group.Projective
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn

import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Point operations and coordinate transfers used by the verification windows. -/

@[expose] public section

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
  · rw [eu, e2, e1]; simp (disch := decide) only [pt, Function.update_self, Function.update_of_ne]
  · intro j hj
    have h0 : j ≠ 0 := by intro h; subst j; contradiction
    have h1 : j ≠ 1 := by intro h; subst j; contradiction
    have h2 : j ≠ 2 := by intro h; subst j; contradiction
    rw [eu, e2, e1, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]

/-- The exact slot transformation of the shared projective addition. -/
def addEnv (e : VG.Proof.X448.X86_64.Env) :=
  evalOps addAffineOps (evalOp (.mul 2 2 10) e)

theorem addEnv_eval (e : VG.Proof.X448.X86_64.Env) :
    pt (addEnv e) 3 4 5 = addWith (e 11) (pt e 0 1 2) (pt e 8 9 10) := by
  rw [addEnv, Point64.addAffineOps_eval, Point64.addWith_affine]
  rfl

theorem addEnv_d (e : VG.Proof.X448.X86_64.Env) : addEnv e 11 = e 11 := rfl

/-- Reusing the affine formula computes the projective sum for arbitrary coordinates. -/
theorem add_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F) {P : Point64.Ops}
    (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) (hd : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (Window.add F P) s fun u => Keep base s u ∧ E u.mem base = addEnv (E s.mem base) := by
  rw [Window.add]
  refine WP.seq (WP.mono (Point64.fop_frame hf hs (.mul 2 2 10) (by decide))
    fun v ⟨kv, ev, _⟩ => ?_)
  have dv : E v.mem base 11 = Spec.Ed448.d := by rw [ev]; exact hd
  refine WP.mono (hP.add (kv.scr hs) dv) fun u ⟨ku, eu⟩ => ⟨kv.trans ku, ?_⟩
  rw [eu, ev]
  rfl

def dbl5Pt (p : Spec.Ed448.Point) := double (double (double (double (double p))))

theorem dbl5_ok {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (dbl5 P) s fun u => Keep base s u ∧
      pt (E u.mem base) 0 1 2 = dbl5Pt (pt (E s.mem base) 0 1 2) ∧
      ∀ j : Index, 3 ≤ j.val → j.val < 12 → E u.mem base j = E s.mem base j := by
  rw [dbl5]
  refine WP.seq (WP.mono (hP.dbl hs) fun s1 ⟨k1, e1⟩ => ?_)
  refine WP.seq (WP.mono (hP.dbl (k1.scr hs)) fun s2 ⟨k2, e2⟩ => ?_)
  refine WP.seq (WP.mono (hP.dbl (k2.scr (k1.scr hs))) fun s3 ⟨k3, e3⟩ => ?_)
  refine WP.seq (WP.mono (hP.dbl (k3.scr (k2.scr (k1.scr hs)))) fun s4 ⟨k4, e4⟩ => ?_)
  refine WP.mono (hP.dbl (k4.scr (k3.scr (k2.scr (k1.scr hs))))) fun u ⟨ku, eu⟩ => ?_
  refine ⟨(((k1.trans k2).trans k3).trans k4).trans ku, ?_, ?_⟩
  · rw [eu, doubleOps_eval, e4, doubleOps_eval, e3, doubleOps_eval, e2, doubleOps_eval, e1, doubleOps_eval]; rfl
  · intro j hj hj'
    rw [eu, doubleOps_keep _ _ (Or.inl ⟨hj, hj'⟩), e4, doubleOps_keep _ _ (Or.inl ⟨hj, hj'⟩), e3, doubleOps_keep _ _ (Or.inl ⟨hj, hj'⟩),
      e2, doubleOps_keep _ _ (Or.inl ⟨hj, hj'⟩), e1, doubleOps_keep _ _ (Or.inl ⟨hj, hj'⟩)]

theorem dbl5Pt_rep {p : Spec.Ed448.Point} {a : EdwardsLaw.EPoint dZ} (h : Rep p a) :
    Rep (dbl5Pt p) ((32 : Nat) • a) := by
  have h4 := double_rep (double_rep (double_rep (double_rep (double_rep h))))
  simpa only [dbl5Pt, ← two_nsmul, smul_smul, Nat.reduceMul] using h4

end VG.Proof.Ed448.X86_64.Window
