import VerifiedGarbage.Proof.Weierstrass.X86.WinJacAccum

/-! Branchless field selection in the arithmetic environment. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem choose_field_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr}
    {size wk m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hW : WkOk F M m size wk Sl) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {o a b : Nat} (ho : Sl o) (ha : a∈V) (hb : b∈V)
    (c : Bool) (hc : s.gpr .ecx=bmask c) :
    WP isa (.block (sel (2*M.n) o a b)) s fun t =>
      ProgKeep M base wk [o] s t ∧
      Inv M base size m Sl (o::V) (Function.update E o (if c then E b else E a)) t := by
  have sep (x : Nat) (hx : x∈V) : o≤x ∨ x+8*M.n≤o := by
    by_cases he : o=x
    · exact Or.inl (Nat.le_of_eq he)
    · have := hL.apart o x ho (hI.sl x hx) he
      omega
  refine WP.mono (selWords_ok hI.scr c hc (hL.le o ho) (hL.le a (hI.sl a ha))
    (hL.le b (hI.sl b hb)) (sep a ha) (sep b hb)) fun t ⟨et,kt,ot⟩ => ?_
  have hk : ProgKeep M base wk [o] s t := ⟨fun r hr => kt.gpr r (fun he => hr (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl <;> simp [clob])),kt.rd,kt.wr,Outs.of_outside ot (by simp [progW])⟩
  refine ⟨hk,hI.update hL hW ho hk ?_ ?_⟩
  · rw [et]; cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact hI.lt a ha
    · exact hI.lt b hb
  · rw [et]; cases c <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact hI.val a ha
    · exact hI.val b hb

theorem keep_of_ckeeps {M : Mod} {base : Addr} {wk : Nat} {s t : State}
    (hk : CKeeps clob s t) : ProgKeep M base wk [] s t :=
  ⟨hk.1,hk.2.2.1,hk.2.2.2,fun _ _ => congrFun hk.2.1 _⟩

end VG.Proof.Weierstrass.X86.JWin
