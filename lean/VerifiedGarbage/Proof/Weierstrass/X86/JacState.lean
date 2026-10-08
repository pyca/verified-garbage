import VerifiedGarbage.Impl.Weierstrass.X86.Jacobian
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86.TCombInv

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86
open VG.Impl.Weierstrass VG.Proof.Mont.X86 VG.Proof.Mont Spec.Weierstrass

/-- A field copy updates the same environment used by arithmetic operations. -/
theorem copyField_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hW : WkOk F M m size wk Sl)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {o a : Nat} (ho : Sl o) (ha : a ∈ V) :
    WP isa (.block (copy (2 * M.n) o a)) s fun t =>
      CKeep M base wk o s t ∧ Inv M base size m Sl (o :: V) (Function.update E o (E a)) t := by
  have hap : o ≤ a ∨ a + 8 * M.n ≤ o := by
    by_cases he : o = a
    · exact Or.inl (by omega)
    · have h := hL.apart o a ho (hI.sl a ha) he
      omega
  refine WP.mono (copyWords_ok (n := M.n) hI.scr (hL.le o ho) (hL.le a (hI.sl a ha))
    hap) fun t ⟨hv,hk,hO⟩ => ?_
  have hkeep : CKeep M base wk o s t :=
    ⟨fun r hr => hk.gpr r (fun he => hr (by
        rw [List.mem_singleton] at he
        subst he
        simp [clob])),hk.rd,hk.wr,Outs.of_outside hO (by simp)⟩
  refine ⟨hkeep,hI.update hL hW ho (ProgKeep.of_op hkeep) ?_ ?_⟩
  · rw [hv]; exact hI.lt a ha
  · rw [hv]; exact hI.val a ha

/-- Setting a canonical field constant also uses the arithmetic environment. -/
theorem setField_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hW : WkOk F M m size wk Sl)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {o v : Nat} (ho : Sl o) (hv : v < m)
    (hR : m < 2 ^ (64 * M.n)) :
    WP isa (.block (setConst M.n o v)) s fun t =>
      CKeep M base wk o s t ∧ Inv M base size m Sl (o :: V)
        (Function.update E o (toM m (2 ^ (64 * M.n)) v)) t := by
  refine WP.mono (setConst_ok hI.scr (hL.le o ho) (Nat.lt_trans hv hR))
    fun t ⟨he,hk,hO⟩ => ?_
  have hkeep : CKeep M base wk o s t :=
    ⟨fun r hr => hk.gpr r (fun he => hr (by
        rw [List.mem_singleton] at he
        subst he
        simp [clob])),hk.rd,hk.wr,Outs.of_outside hO (by simp)⟩
  refine ⟨hkeep,hI.update hL hW ho (ProgKeep.of_op hkeep) ?_ ?_⟩
  · rw [he]; exact hv
  · rw [he]

theorem progKeep_of_op {M : Mod} {base : Addr} {wk : Nat} {W : List Nat} {o : Nat} {s t : State}
    (h : CKeep M base wk o s t) (ho : o ∈ W) : ProgKeep M base wk W s t :=
  (ProgKeep.of_op h).mono (by intro x hx; rw [List.mem_singleton.mp hx]; exact ho)

/-- Copying a point retains its coordinates and the field environment. -/
theorem copyPoint_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m]
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hW : WkOk F M m size wk Sl)
    {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (.block (copyPt M.n o q)) s fun t =>
      ∃ E', ProgKeep M base wk (rcbW S o) s t ∧
      Inv M base size m Sl ([o.x,o.y,o.z] ++ V) E' t ∧
      (E' o.x,E' o.y,E' o.z) = (E q.x,E q.y,E q.z) := by
  have hn : [o.x,o.y,o.z].Nodup := hA.nodup.drop (i := 6)
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,
    or_false,not_or,List.nodup_nil,and_true] at hn
  have hqa : ∀ x ∈ [q.x,q.y,q.z], ∀ y ∈ [o.x,o.y,o.z], x ≠ y := by
    intro x hx y hy he
    have hro : x ∈ rcbR S p q := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [rcbR]
    apply hA.apart x hro
    rw [he]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl <;> simp [rcbW]
  have hox : Sl o.x := hSl o.x (by simp [rcbW])
  have hoy : Sl o.y := hSl o.y (by simp [rcbW])
  have hoz : Sl o.z := hSl o.z (by simp [rcbW])
  have hqx := hV q.x (by simp [rcbR])
  have hqy := hV q.y (by simp [rcbR])
  have hqz := hV q.z (by simp [rcbR])
  rw [copyPt,List.append_assoc,WP.block_append_iff]
  refine WP.mono (copyField_ok hL hW hI hox hqx) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyField_ok hL hW ia hoy (List.mem_cons_of_mem _ hqy)) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (copyField_ok hL hW ib hoz
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hqz))) fun t ⟨kt,it⟩ => ?_
  refine ⟨_,(progKeep_of_op ka (by simp [rcbW])).trans
    ((progKeep_of_op kb (by simp [rcbW])).trans (progKeep_of_op kt (by simp [rcbW]))),
    it.sub ?_,?_⟩
  · intro x hx
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · simp only [Function.update_self,Function.update_of_ne hn.1.1,
      Function.update_of_ne hn.1.2,Function.update_of_ne hn.2.1,
      Function.update_of_ne (hqa q.y (by simp) o.x (by simp)),
      Function.update_of_ne (hqa q.z (by simp) o.x (by simp)),
      Function.update_of_ne (hqa q.z (by simp) o.y (by simp))]

/-- The infinity branch writes a canonical nonzero y and zero z. -/
theorem infinityPoint_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Spec.Weierstrass.Curve} {base : Addr} {size wk : Nat}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hW : WkOk F K.M C.p size wk Sl)
    {o : Pt} (hSl : ∀ x ∈ [o.x,o.y,o.z], Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hOne : K.one < C.p) :
    WP isa (.block (Jacobian.infinity K o)) s fun t =>
      ∃ E', ProgKeep K.M base wk (rcbW K.S o) s t ∧
      Inv K.M base size C.p Sl ([o.x,o.y,o.z] ++ V) E' t ∧
      InvJ C (E' o.x) (E' o.y) (E' o.z) .infinity := by
  have hR := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hI.mod.val] at hR
  have h0 : 0 < C.p := Nat.pos_of_ne_zero (NeZero.ne C.p)
  rw [Jacobian.infinity,List.append_assoc,WP.block_append_iff]
  refine WP.mono (setField_ok hL hW hI (hSl o.x (by simp)) h0 hR) fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setField_ok hL hW ia (hSl o.y (by simp)) hOne hR) fun b ⟨kb,ib⟩ => ?_
  refine WP.mono (setField_ok hL hW ib (hSl o.z (by simp)) h0 hR) fun t ⟨kt,it⟩ => ?_
  refine ⟨_,(progKeep_of_op ka (by simp [rcbW])).trans
    ((progKeep_of_op kb (by simp [rcbW])).trans (progKeep_of_op kt (by simp [rcbW]))),
    it.sub ?_,Or.inl ⟨rfl,?_⟩⟩
  · intro x hx
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · rw [Function.update_self]
    simp only [toM, Fin.ofNat_zero, Lean.Grind.Semiring.zero_mul]


end VG.Proof.Weierstrass.X86
