import VerifiedGarbage.Proof.Weierstrass.X86_64.NafCachePoint
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero

/-! Negating a selected point leaves its cached powers of Z unchanged. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

def CachedPoint (C : Curve) (E : Nat → Fe C) (p : Pt) (dst : Nat) (P : Point C) : Prop :=
  InvJ C (E p.x) (E p.y) (E p.z) P ∧ E dst=E p.z*E p.z ∧ E (dst+32)=E dst*E p.z

def CachedPost (M : Mod) (base : Addr) (size : Nat) (C : Curve) (Sl : Nat → Prop)
    (V : List Nat) (p : Pt) (dst : Nat) (P : Point C) (s t : State) : Prop :=
  ProgKeep M base (cachedSlots p dst) s t ∧
  Inv M base size C.p Sl (cachedSlots p dst++V) (tmv C M.n base t) t ∧
  CachedPoint C (tmv C M.n base t) p dst P

theorem CachedPoint.to_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv M base size C.p Sl V E s) {p : Pt} {dst : Nat} {P : Point C}
    (hV : ∀ x∈cachedSlots p dst,x∈V) (hP : CachedPoint C E p dst P) :
    CachedPoint C (tmv C M.n base s) p dst P := by
  unfold CachedPoint tmv
  rw [hI.val _ (hV _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hV _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hV _ (by simp [cachedSlots,jacCoords])),
    hI.val _ (hV _ (by simp [cachedSlots])),hI.val _ (hV _ (by simp [cachedSlots]))]
  exact hP

theorem CachedPost.prefix {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {p : Pt} {dst : Nat} {P : Point C} {s t u : State}
    (h : CachedPost M base size C Sl V p dst P t u)
    (hk : ProgKeep M base (cachedSlots p dst) s t) : CachedPost M base size C Sl V p dst P s u :=
  ⟨hk.trans h.1,h.2⟩

theorem negCachedPoint_ok {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} (hL : Lay M size Sl) (hm : UnitMod C.p (2^(64*M.n)))
    {p : Pt} {dst zslot : Nat} (hxy : p.x≠p.y) (hzy : p.z≠p.y)
    (hd2 : dst≠p.y) (hd3 : dst+32≠p.y)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv M base size C.p Sl (cachedSlots p dst++V) E s)
    (hz : zslot∈cachedSlots p dst++V) (he0 : E zslot=0)
    {P : Point C} (hP : CachedPoint C E p dst P) :
    WP isa (.block (VG.Impl.Mont.X86_64.sub M p.y zslot p.y)) s
      (CachedPost M base size C Sl V p dst (negPt P) s) := by
  have hyp : p.y∈cachedSlots p dst++V := by simp [cachedSlots,jacCoords]
  have hS : ∀ x∈(FOp.sub p.y zslot p.y).out::(FOp.sub p.y zslot p.y).ins,Sl x := by
    intro x hx
    simp only [FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact hI.sl _ hyp
    · exact hI.sl _ hz
    · exact hI.sl _ hyp
  have hR : ∀ x∈(FOp.sub p.y zslot p.y).ins,x∈cachedSlots p dst++V := by
    intro x hx
    simp only [FOp.ins,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact hz
    · exact hyp
  refine WP.mono (fop_ok hL hm hI hS hR) fun t ⟨kt,it⟩ => ?_
  have iv := it.sub (fun x hx => List.mem_cons_of_mem _ hx)
  refine ⟨progKeep_of_op kt (by simp [cachedSlots,jacCoords,FOp.out]),iv.to_tmv,
    CachedPoint.to_tmv iv (fun x hx => List.mem_append_left _ hx) ?_⟩
  simp only [CachedPoint,FOp.run,Function.update_self,Function.update_of_ne hxy,
    Function.update_of_ne hzy,Function.update_of_ne hd2,Function.update_of_ne hd3,he0,
    show (0 : Fe C)-E p.y = -E p.y from by grind]
  exact ⟨hP.1.negY,hP.2⟩

end VG.Proof.Weierstrass.X86_64
