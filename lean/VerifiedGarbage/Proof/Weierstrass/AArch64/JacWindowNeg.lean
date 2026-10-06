import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit

/-! Signed field selections for public Jacobian windows. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps)

/-- A masked field selection updates the arithmetic environment, including
when its destination aliases one of its source slots. -/
theorem selectField_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    {o a b : Nat} (ho : Sl o) (ha : a ∈ V) (hb : b ∈ V)
    (c : Bool) (hc : s.gpr .x3 = bmask c) :
    WP isa (.block (sel M.n o a b)) s fun t =>
      OpKeep M base o s t ∧ Inv M base size m Sl (o::V)
        (Function.update E o (if c then E b else E a)) t := by
  have hap (x : Nat) (hx : Sl x) : o ≤ x ∨ x+8*M.n ≤ o := by
    by_cases h : o=x
    · omega
    · have := hL.apart o x ho hx h; omega
  refine WP.mono (sel_ok c M.n hI.scr hc (hL.le o ho)
    (hL.le a (hI.sl a ha)) (hL.le b (hI.sl b hb)) (hAl.sl o ho)
    (hAl.sl a (hI.sl a ha)) (hAl.sl b (hI.sl b hb))
    (hap a (hI.sl a ha)) (hap b (hI.sl b hb))) fun t ⟨hv,hk,hO⟩ => ?_
  have kp : OpKeep M base o s t := by
    refine ⟨fun r hr => hk.gpr r (fun hh => hr ?_),hk.rd,hk.wr,hk.sp,fun x hx _ => hO x hx⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl | rfl <;> simp [clob]
  refine ⟨kp,hI.update hL ho kp ?_ ?_⟩
  · rw [hv]; cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact hI.lt a ha
    · exact hI.lt b hb
  · rw [hv]; cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact hI.val a ha
    · exact hI.val b hb

/-- Negate a coordinate exactly when the public scalar digit is negative.
The bit table is framed across the temporary subtraction. -/
theorem negFieldWindow_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    (hm : UnitMod m (2^(64*M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {neg z y w bits k j N : Nat}
    (hneg : Sl neg) (hz : z ∈ V) (hy : y ∈ V) (hny : neg ≠ y) (hzero : E z=0)
    (hw1 : 1 ≤ w) (hw : w<65536) (hj : w*j+w ≤ N)
    (hN : bits+N ≤ size) (hbw : bits+w-1<4096)
    (hx : s.gpr .x19=BitVec.ofNat 64 j)
    (hbits : ∀ t<N, s.mem (off base (bits+t))=if k.testBit t then 1 else 0)
    (hbn : bits+N ≤ neg ∨ neg+8*M.n ≤ bits)
    (hbt : bits+N ≤ M.tmp ∨ M.tmp+8*M.n ≤ bits) :
    WP isa (.block (negYW M w neg z y bits)) s fun t =>
      ProgKeep M base [neg,y] s t ∧
      Inv M base size m Sl (y::neg::V)
        (Function.update (Function.update E neg (-E y)) y
          (if decide (combWin w k j < 2^(w-1)) then -E y else E y)) t := by
  have hn := hI.scr.nowrap
  rw [negYW,List.append_assoc,WP.block_append_iff]
  have hsl : ∀ x ∈ (FOp.sub neg z y).out :: (FOp.sub neg z y).ins, Sl x := by
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact hneg
    · exact hI.sl _ hz
    · exact hI.sl _ hy
  have hr : ∀ x ∈ (FOp.sub neg z y).ins, x ∈ V := by
    intro x hx
    simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> with_reducible assumption
  refine WP.mono (fop_ok hL hAl hm hI hsl hr) fun a ⟨ka,ia⟩ => ?_
  have hb : ∀ t<N, a.mem (off base (bits+t))=if k.testBit t then 1 else 0 := by
    intro t ht
    rw [ka.unch.byte (fun q hq => ?_) (by omega)]
    · exact hbits t ht
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl <;> dsimp only [FOp.out] <;> omega
  have h19 : a.gpr .x19=BitVec.ofNat 64 j := by rw [ka.gpr _ (x19_not_clob _),hx]
  rw [WP.block_append_iff]
  refine WP.mono (signMaskW_ok ia.scr w bits hw1 hw hj hN hbw h19 hb) fun b ⟨b3,kb⟩ => ?_
  have ib := ia.of_keeps kb (by decide)
  refine WP.mono (selectField_ok hL hAl ib (hI.sl y hy)
    (List.mem_cons_of_mem _ hy) (List.mem_cons_self ..) _ b3) fun t ⟨kt,it⟩ => ?_
  have kpb : ProgKeep M base [neg,y] a b := by
    refine ⟨fun r hr => kb.gpr r (fun hh => hr ?_),kb.rd,kb.wr,kb.sp,fun _ _ _ => congrFun kb.mem _⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl | rfl <;> simp [clob]
  refine ⟨(progKeep_of_op ka (by simp [FOp.out])).trans (kpb.trans (progKeep_of_op kt (by simp))),?_⟩
  simpa only [FOp.out,FOp.run,hzero,show (0 : Fin m)-E y = -E y by grind,
    Function.update_self,Function.update_of_ne (Ne.symm hny)] using it

end VG.Proof.Weierstrass.AArch64
