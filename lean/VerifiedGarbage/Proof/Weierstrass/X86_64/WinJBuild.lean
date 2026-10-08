import VerifiedGarbage.Impl.Weierstrass.X86_64.WindowJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.Weierstrass.WindowJ

/-!
# Windows in Jacobian coordinates on x86-64: the slots

The field programs of the Jacobian window method are on slots that are apart
(`WinLay.rcbApart_winJ`), and the table is apart from what the loop writes
(`tbl_apart_loopW`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- The slots the Jacobian window method's field programs use are apart:
the doublings between `R` and `D`, and `fromJ` from `R` into `D` (`z` the
slots of zero). -/
theorem _root_.VG.Proof.Weierstrass.WinLay.rcbApart_winJ {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    RcbApart K.S K.R K.R K.D ∧ RcbApart K.S K.D K.D K.R ∧
      RcbApart K.S K.R ⟨K.zero, K.zero, K.zero⟩ K.D := by
  have hnd := hL.nodup
  have ha := hL.ro K.S.a (by simp [winRo])
  have hb := hL.ro K.S.b3 (by simp [winRo])
  have hz := hL.ro K.zero (by simp [winRo])
  simp only [winOther, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd ha hb hz
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [rcbW, rcbR, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, forall_eq_or_imp, forall_eq] <;> grind

/-- A table slot is apart from what the loop's field programs write. -/
theorem tbl_apart_loopW {K : WinCfg} {size : Nat} (hL : WinLay K size) {j : Nat} (hj1 : 1 ≤ j) (hj8 : j ≤ 8)
    {x : Nat} (hx : x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z]) :
    ∀ w ∈ loopW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K hj1 hj8 x hx
  intro w hw
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact (hL.tbl_apart (List.mem_append_right _ hy) hi).symm
  · exact hL.lay.tmp _ (by simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi))

/-- The slots of a point, written. -/
theorem pt_other {K : WinCfg} {p : Pt} (h : p = K.R ∨ p = K.E ∨ p = K.D) :
    ∀ x ∈ [p.x, p.y, p.z], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases h with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> win_mem

end VG.Proof.Weierstrass.X86_64
