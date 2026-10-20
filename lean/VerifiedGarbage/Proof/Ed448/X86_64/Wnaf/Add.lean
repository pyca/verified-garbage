module

public import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Select
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
import VerifiedGarbage.Proof.Ed448.X86_64.Wnaf.Coords
import VerifiedGarbage.Proof.Ed448.X86_64.Window.Ops
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-! Optional additions for the nonzero signed digits. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64
open VG.Proof.X448.X86_64
open VG.Proof.Ed448.X86_64.Window (accept_ok tablePoint add_ok addEnv_d addEnv_eval)

private theorem baseBody_ok {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) {t : Nat} {d : Int} (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .rbx = BitVec.ofNat 64 t) (hm : s.mem (off base (SDIG + t)) = CodeByte d)
    (hi : s.gpr .r15 = DigitWord d) (hc : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (.seq selectBase (.seq P.add (.block Window.accept))) s fun u => Keep base s u ∧
      E u.mem base 11 = Spec.Ed448.d ∧ pt (E u.mem base) 0 1 2 =
        Spec.Ed448.pointAdd (pt (E s.mem base) 0 1 2) (Proof.X448.basePt (baseEntry d)) := by
  refine WP.seq (WP.mono (selectBase_ok hs ht hd hr hm hi) fun a ⟨ka, pa, fa⟩ => ?_)
  have ac : E a.mem base 11 = Spec.Ed448.d := by rw [fa 11 (by decide) (by decide) (by decide) (by decide), hc]
  have ap : pt (E a.mem base) 0 1 2 = pt (E s.mem base) 0 1 2 :=
    pt_congr (fa 0 (by decide) (by decide) (by decide) (by decide))
      (fa 1 (by decide) (by decide) (by decide) (by decide))
      (fa 2 (by decide) (by decide) (by decide) (by decide))
  refine WP.seq (WP.mono (hP.add (ka.scr hs) ac) fun b ⟨kb, eb⟩ => ?_)
  refine WP.mono (accept_ok (kb.scr (ka.scr hs))) fun u ⟨ku, pu, fu⟩ => ?_
  refine ⟨(ka.trans kb).trans ku, ?_, ?_⟩
  · rw [fu 11 (by decide), eb, Point64.addAffineOps_keep _ _ (Or.inr (Or.inl (by decide))), ac]
  · have px := congrArg Prod.fst pa
    have py := congrArg Prod.snd pa
    dsimp only at px py
    rw [pu, eb, Point64.addAffineOps_eval, ac, addWith_d, ap, px, py]
    rfl

private theorem keyBody_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F)
    {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) {t : Nat} {d : Int} (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .rbx = BitVec.ofNat 64 t) (hm : s.mem (off base (KDIG + t)) = CodeByte d)
    (hi : s.gpr .r15 = DigitWord d) (hc : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (.seq selectKey (.seq (Window.add F P) (.block Window.accept))) s fun u => Keep base s u ∧
      E u.mem base 11 = Spec.Ed448.d ∧ pt (E u.mem base) 0 1 2 =
        Spec.Ed448.pointAdd (pt (E s.mem base) 0 1 2)
          (SignedWindow.signedPoint (decide (d < 0)) (tablePoint s.mem base d.natAbs)) := by
  refine WP.seq (WP.mono (selectKey_ok hs ht hd hr hm hi) fun a ⟨ka, pa, fa⟩ => ?_)
  have ac : E a.mem base 11 = Spec.Ed448.d := by
    rw [fa 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hc]
  have ap : pt (E a.mem base) 0 1 2 = pt (E s.mem base) 0 1 2 :=
    pt_congr (fa 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fa 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fa 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine WP.seq (WP.mono (add_ok hf hP (ka.scr hs) ac) fun b ⟨kb, eb⟩ => ?_)
  refine WP.mono (accept_ok (kb.scr (ka.scr hs))) fun u ⟨ku, pu, fu⟩ => ?_
  refine ⟨(ka.trans kb).trans ku, ?_, ?_⟩
  · rw [fu 11 (by decide), eb, addEnv_d, ac]
  · rw [pu, eb, addEnv_eval, ac, addWith_d, ap, pa]

def maybeAdd (d : Int) (p q : Spec.Ed448.Point) : Spec.Ed448.Point :=
  if d = 0 then p else Spec.Ed448.pointAdd p q

theorem addBase_ok {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) {t : Nat} {d : Int} (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .rbx = BitVec.ofNat 64 t) (hm : s.mem (off base (SDIG + t)) = CodeByte d)
    (hc : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (addBase P) s fun u => Keep base s u ∧ E u.mem base 11 = Spec.Ed448.d ∧
      pt (E u.mem base) 0 1 2 = maybeAdd d (pt (E s.mem base) 0 1 2) (Proof.X448.basePt (baseEntry d)) := by
  refine WP.seq (WP.mono (getDigit_ok hs (by simp only [SDIG]; omega) hd hr hm) fun a ⟨ar, az, ak⟩ => ?_)
  have ka : Keep base s a := keeps_keep (ak.mono (by decide))
  refine WP.ite (!decide (d = 0)) (by simp only [eval, az, Option.map_some]) (fun hz => ?_) (fun hz => ?_)
  · have hn : d ≠ 0 := by simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hz
    refine WP.mono (baseBody_ok hP (ka.scr hs) ht hd ((ka.gpr _ (by decide)).trans hr)
      (by rw [ak.2.1]; exact hm) ar (by rw [ak.2.1]; exact hc)) fun u ⟨ku, du, pu⟩ => ?_
    refine ⟨ka.trans ku, du, ?_⟩
    rw [pu, ak.2.1, maybeAdd, ite_eq_right hn]
  · have he : d = 0 := by simpa only [Bool.not_eq_false', decide_eq_true_eq] using hz
    refine WP.block_nil ⟨ka, ?_, ?_⟩
    · rw [ak.2.1]; exact hc
    · rw [maybeAdd, ite_eq_left he, ak.2.1]

theorem addKey_ok {F : Impl.X448.X86_64.Field} (hf : FieldOk F)
    {P : Point64.Ops} (hP : Point64.PointOk P) {s : State} {base : Addr}
    (hs : Scr s base) {t : Nat} {d : Int} (ht : t < 461) (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .rbx = BitVec.ofNat 64 t) (hm : s.mem (off base (KDIG + t)) = CodeByte d)
    (hc : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (addKey F P) s fun u => Keep base s u ∧ E u.mem base 11 = Spec.Ed448.d ∧
      pt (E u.mem base) 0 1 2 = maybeAdd d (pt (E s.mem base) 0 1 2)
        (SignedWindow.signedPoint (decide (d < 0)) (tablePoint s.mem base d.natAbs)) := by
  refine WP.seq (WP.mono (getDigit_ok hs (by simp only [KDIG]; omega) hd hr hm) fun a ⟨ar, az, ak⟩ => ?_)
  have ka : Keep base s a := keeps_keep (ak.mono (by decide))
  refine WP.ite (!decide (d = 0)) (by simp only [eval, az, Option.map_some]) (fun hz => ?_) (fun hz => ?_)
  · have hn : d ≠ 0 := by simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using hz
    refine WP.mono (keyBody_ok hf hP (ka.scr hs) ht hd ((ka.gpr _ (by decide)).trans hr)
      (by rw [ak.2.1]; exact hm) ar (by rw [ak.2.1]; exact hc)) fun u ⟨ku, du, pu⟩ => ?_
    refine ⟨ka.trans ku, du, ?_⟩
    rw [pu, ak.2.1, maybeAdd, ite_eq_right hn]
  · have he : d = 0 := by simpa only [Bool.not_eq_false', decide_eq_true_eq] using hz
    refine WP.block_nil ⟨ka, ?_, ?_⟩
    · rw [ak.2.1]; exact hc
    · rw [maybeAdd, ite_eq_left he, ak.2.1]

end VG.Proof.Ed448.X86_64.Wnaf
