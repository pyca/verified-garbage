import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState

/-! Branchless field selection with an exact environment update. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem selectField_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {o a b : Nat}
    (ho : Sl o) (ha : a∈V) (hb : b∈V) (c : Bool) (hc : s.gpr .rcx=if c then BitVec.allOnes 64 else 0) :
    WP isa (.block (sel M.n o a b)) s fun t =>
      ProgKeep M base [o] s t ∧
      Inv M base size m Sl (o::V) (Function.update E o (if c then E b else E a)) t := by
  have sep : ∀ x,Sl x → o≤x ∨ x+8*M.n≤o := by
    intro x hx
    by_cases he : o=x
    · exact Or.inl (by omega)
    · have := hL.apart o x ho hx he
      omega
  refine WP.mono (sel_ok c M.n hI.scr hc (hL.le o ho)
    (hL.le a (hI.sl a ha)) (hL.le b (hI.sl b hb))
    (sep a (hI.sl a ha)) (sep b (hI.sl b hb))) fun t ⟨vt,kt,ot⟩ => ?_
  have kop : OpKeep M base o s t := by
    refine ⟨fun r hr => kt.gpr r ?_,kt.rd,kt.wr,fun x hx _ => ot x hx⟩
    intro hh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl <;> exact hr (by simp [clob])
  refine ⟨progKeep_of_op kop (by simp),hI.update hL ho kop ?_ ?_⟩
  · rw [vt]
    cases c
    · exact hI.lt a ha
    · exact hI.lt b hb
  · rw [vt]
    cases c
    · exact hI.val a ha
    · exact hI.val b hb

end VG.Proof.Weierstrass.X86_64
