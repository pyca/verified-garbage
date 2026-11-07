module

import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Timing
public import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Jacobian
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.PointOpsContract

/-! Exceptional branches on public Jacobian coordinates preserve a shared,
exact field environment, including the infinity and point-copy branches. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64

abbrev FieldCT (c : Prog isa) :=
  ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0])) c

def copyPointEnv {F : Type _} (E : Nat → F) (o q : Pt) : Nat → F :=
  let e₁ := Function.update E o.x (E q.x)
  let e₂ := Function.update e₁ o.y (e₁ q.y)
  Function.update e₂ o.z (e₂ q.z)

theorem copyPoint_relCT {M : Mod} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hAl : Aligned M Sl)
    {o q : Pt} (hSl : ∀ x∈[o.x,o.y,o.z], Sl x)
    {V : List Nat} {E : Nat → Fin m} (hV : ∀ x∈[q.x,q.y,q.z], x∈V)
    (hct : FieldCT (.block (copyPt M.n o q))) :
    RelCT isa (FieldPair M base size m Sl V E) (.block (copyPt M.n o q))
      (FieldPair M base size m Sl ([o.x,o.y,o.z]++V) (copyPointEnv E o q)) := by
  apply fieldWP_relCT hct
  intro s hi
  rw [copyPt,List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAl hi (hSl _ (by simp)) (hV _ (by simp))) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hAl ia (hSl _ (by simp))
    (List.mem_cons_of_mem _ (hV _ (by simp)))) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (copyField_ok hL hAl ib (hSl _ (by simp))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hV _ (by simp))))) fun t ⟨kt,it⟩ => ?_
  refine ⟨it.sub ?_,kt.sp.trans (kb.sp.trans ka.sp)⟩
  intro x hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

def infinityEnv (M : Mod) (m one : Nat) [NeZero m] (E : Nat → Fin m) (o : Pt) : Nat → Fin m :=
  Function.update (Function.update (Function.update E o.x (toM m (2^(64*M.n)) 0))
    o.y (toM m (2^(64*M.n)) one)) o.z (toM m (2^(64*M.n)) 0)

theorem infinity_relCT {K : WinCfg} {base : Addr} {size m : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hAl : Aligned K.M Sl)
    {o : Pt} (hSl : ∀ x∈[o.x,o.y,o.z], Sl x) (hOne : K.one<m)
    {V : List Nat} {E : Nat → Fin m} (hct : FieldCT (.block (Jacobian.infinity K o))) :
    RelCT isa (FieldPair K.M base size m Sl V E) (.block (Jacobian.infinity K o))
      (FieldPair K.M base size m Sl ([o.x,o.y,o.z]++V) (infinityEnv K.M m K.one E o)) := by
  apply fieldWP_relCT hct
  intro s hi
  have hR := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hi.mod.val] at hR
  have h0 : 0<m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [Jacobian.infinity,List.append_assoc,WP.block_append_iff]
  refine WP.mono (setField_ok hL hAl hi (hSl _ (by simp)) h0 hR) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setField_ok hL hAl ia (hSl _ (by simp)) hOne hR) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (setField_ok hL hAl ib (hSl _ (by simp)) h0 hR) fun t ⟨kt,it⟩ => ?_
  refine ⟨it.sub ?_,kt.sp.trans (kb.sp.trans ka.sp)⟩
  intro x hx
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

end VG.Proof.Weierstrass.AArch64
