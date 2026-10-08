import VerifiedGarbage.Proof.Weierstrass.X86.FieldTiming
import VerifiedGarbage.Proof.Weierstrass.X86.JacAdd

/-! Exact common field environments for the exceptional point-addition branches. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86 VG.Proof.Mont VG.Proof.Mont.X86

def copyPointEnv {F : Type _} (E : Nat → F) (o q : Pt) : Nat → F :=
  let e₁ := Function.update E o.x (E q.x)
  let e₂ := Function.update e₁ o.y (e₁ q.y)
  Function.update e₂ o.z (e₂ q.z)

theorem copyPoint_relCT {counter : BitVec 32} {FM : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hW : WkOk FM M m size wk Sl)
    {o q : Pt} (hSl : ∀ x∈[o.x,o.y,o.z], Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈[q.x,q.y,q.z], x∈V)
    (hct : ScratchCT (.block (copyPt M.n o q))) :
    RelCT isa (FieldPair M base size m Sl V E counter) (.block (copyPt M.n o q))
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (copyPointEnv E o q) counter) := by
  apply fieldProgram_relCT hct
  intro s hi
  rw [copyPt,List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyField_ok hL hW hi (hSl _ (by simp)) (hV _ (by simp))) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hW ia (hSl _ (by simp))
    (List.mem_cons_of_mem _ (hV _ (by simp)))) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (copyField_ok hL hW ib (hSl _ (by simp))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hV _ (by simp))))) fun t ⟨kt,it⟩ => ?_
  refine ⟨ka.keeps.trans (kb.keeps.trans kt.keeps),it.sub ?_⟩
  intro x hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

def infinityEnv (M : Mod) (m one : Nat) [NeZero m] (E : Nat → Fin m) (o : Pt) : Nat → Fin m :=
  Function.update (Function.update (Function.update E o.x (toM m (2^(64*M.n)) 0))
    o.y (toM m (2^(64*M.n)) one)) o.z (toM m (2^(64*M.n)) 0)

theorem infinity_relCT {counter : BitVec 32} {FM : Spec.Weierstrass.Mont.Modulus} {wk : Nat} {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hW : WkOk FM K.M m size wk Sl)
    {o : Pt} (hSl : ∀ x∈[o.x,o.y,o.z], Sl x) (hOne : K.one<m)
    {V : List Nat} {E : Nat → Fin m} (hct : ScratchCT (.block (Jacobian.infinity K o))) :
    RelCT isa (FieldPair K.M base size m Sl V E counter) (.block (Jacobian.infinity K o))
      (FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) (infinityEnv K.M m K.one E o) counter) := by
  apply fieldProgram_relCT hct
  intro s hi
  have hR := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hi.mod.val] at hR
  have h0 : 0<m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [Jacobian.infinity,List.append_assoc,WP.block_append_iff]
  refine WP.mono (setField_ok hL hW hi (hSl _ (by simp)) h0 hR) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setField_ok hL hW ia (hSl _ (by simp)) hOne hR) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (setField_ok hL hW ib (hSl _ (by simp)) h0 hR) fun t ⟨kt,it⟩ => ?_
  refine ⟨ka.keeps.trans (kb.keeps.trans kt.keeps),it.sub ?_⟩
  intro x hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

end VG.Proof.Weierstrass.X86
