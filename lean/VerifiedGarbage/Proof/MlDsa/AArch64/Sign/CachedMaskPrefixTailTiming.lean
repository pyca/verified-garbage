import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskPrefixTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMaskTail

namespace VG.Proof.MlDsa.AArch64.Sign.Cached
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Proof.MlKem.AArch64 (Only wp_ldrx wp_nil)
open VG.Proof.MlDsa.Sign

private theorem seqIte_tr {P Q : State→State→Prop} {c : Cond} {a b d : Prog isa}
    (hc : ∀x y,P x y→isa.eval c x=isa.eval c y)
    (ha : RelCT isa (fun x y=>P x y ∧ isa.eval c x=some true) (.seq a d) Q)
    (hb : RelCT isa (fun x y=>P x y ∧ isa.eval c x=some false) (.seq b d) Q) :
    RelCT isa P (.seq (.ite c a b) d) Q := by
  intro x y tx ty u v hp ex ey
  have hcond := hc x y hp
  cases ex with
  | seq ex ed =>
    cases ey with
    | seq ey ef =>
      cases ex with
      | iteT hx ea =>
        cases ey with
        | iteT _ eb =>
          obtain ⟨he,hq⟩ := ha _ _ _ _ _ _ ⟨hp,hx⟩ (.seq ea ed) (.seq eb ef)
          exact ⟨by simpa only [List.cons_append] using congrArg (List.cons (.branch true)) he,hq⟩
        | iteF hy _ => rw [hcond,hy] at hx; cases hx
      | iteF hx ea =>
        cases ey with
        | iteT hy _ => rw [hcond,hy] at hx; cases hx
        | iteF _ eb =>
          obtain ⟨he,hq⟩ := hb _ _ _ _ _ _ ⟨hp,hx⟩ (.seq ea ed) (.seq eb ef)
          exact ⟨by simpa only [List.cons_append] using congrArg (List.cons (.branch false)) he,hq⟩

theorem loadIndex_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : p=mlDsa65∨p=mlDsa87) (h : PositiveICm p S σ t (p.ℓ-1) s) (hm : t=0∨Mask p σ t s) :
    WP isa (.block [.ldr .x .x9 .x28 oKAP]) s fun u =>
      (PositiveICm p S σ t (p.ℓ-1) u ∧ (t=0∨Mask p σ t u)) ∧ u.gpr .x9=BitVec.ofNat 64 (p.ℓ*t) := by
  have hk : inB (sgB p) (sc oKAP) 8=true := by rcases hp with rfl|rfl <;> decide
  have hload : WP isa (.block [.ldr .x .x9 .x28 oKAP]) s fun a =>
      Only [.x9] s a ∧ a.gpr .x9=s.mem.readW (pa s (sc oKAP)) 64 :=
    wp_ldrx (t:=.x9) (n:=.x28) (off:=oKAP) (a:=pa s (sc oKAP))
    (by decide) rfl (h.l.st.lay.inR hk) fun a ha va=>wp_nil ⟨ha,va⟩
  refine WP.mono_syms hload fun u ⟨hu,hv⟩ hy => ?_
  have hP : PPostB S s u [] := postB_of_keep hu.keep (by decide) (by rw [hu.mem];exact Frame.refl _ _)
  exact ⟨⟨h.step hP hy (by rcases hp with rfl|rfl <;> decide),
    cache_keep h.l.st.lay hm hP (by rcases hp with rfl|rfl <;> decide)⟩,hv.trans h.l.kap⟩

theorem copyFinish_tr {p : Params} {S t : Nat} {E : State→State→Prop}
    (hp : p=mlDsa65∨p=mlDsa87) :
    RelCT isa (RootRS p S E fun σ s => PositiveICm p S σ t (p.ℓ-1) s ∧ Mask p σ t s)
      (.seq (Impl.MlDsa.AArch64.Sign.Cached.copyMask p)
        (Impl.MlDsa.AArch64.Sign.Optimized.maskFinish p (p.ℓ-1))) fun _ _ => True := by
  apply RelCT.seq (R := RootRS p S E fun σ s => PositiveICm p S σ t (p.ℓ-1) s ∧
    Fam s (yBase p) (p.ℓ-1+1) (Yv p σ (p.ℓ*t)))
  · apply liftRootR (fun _ _ _ h => copyMask_phase_ok (copyChk_ok hp) h.1 h.2)
    exact lrel_tr (hc := copyHint) (fun _ _ h=>h.1.lrel (fun _ _ h=>h.1.l.st)) (by rcases hp with rfl|rfl <;> taint_decide)
  · apply optimizedMaskFinish_tr (S := S) (show optimizedMaskChk p (p.ℓ-1)=true from by rcases hp with rfl|rfl <;> decide)
    intro x y h
    have L := h.1.lrel (fun _ _ h=>h.1.l.st)
    obtain ⟨σ,τ,_,_,_,_,ix,iy⟩ := h.1
    exact ⟨⟨σ,ix.1.l.st,ix.1.l.k.d.roots⟩,⟨τ,iy.1.l.st,iy.1.l.k.d.roots⟩,
      (ix.2 (p.ℓ-1) (by omega)).1,(iy.2 (p.ℓ-1) (by omega)).1,
      L.regs .x28 (by decide),L.sp,h.2.1⟩

private theorem assocBack {P Q : State→State→Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro x y tx ty u v hp ex ey
  cases ex with
  | seq ex ec =>
    cases ex with
    | seq ea eb =>
      cases ey with
      | seq ey fc =>
        cases ey with
        | seq fa fb =>
          obtain ⟨ht,hq⟩ := h _ _ _ _ _ _ hp (.seq ea (.seq eb ec)) (.seq fa (.seq fb fc))
          exact ⟨by simpa only [List.append_assoc] using ht,hq⟩

theorem tailMask_tr {P : Prims} {S t : Nat} {E : State→State→Prop}
    (hP : PrimsOk P S) {p : Params} (hp : p=mlDsa65∨p=mlDsa87) :
    RelCT isa (RootRS p S E fun σ s=>PositiveICm p S σ t (p.ℓ-1) s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.tailMask P p)
      (RootRS p S E (PositiveICm p S · t p.ℓ)) := by
  apply liftRootR (fun _ _ _ h=>tailMask_ok hP hp h.1 h.2)
  unfold Impl.MlDsa.AArch64.Sign.Cached.tailMask
  apply RelCT.seq (R := RootRS p S E fun σ s=>
    (PositiveICm p S σ t (p.ℓ-1) s ∧ (t=0∨Mask p σ t s)) ∧ s.gpr .x9=BitVec.ofNat 64 (p.ℓ*t))
  · apply liftRootR (fun _ _ _ h=>loadIndex_ok hp h.1 h.2)
    exact lrel_tr (fun _ _ h=>h.1.lrel (fun _ _ h=>h.1.l.st)) (by taint_decide)
  · apply seqIte_tr
    · intro x y h
      obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1
      change some (x.gpr .x9 != 0)=some (y.gpr .x9 != 0)
      rw [hx.2,hy.2]
    · apply RelCT.mono (copyFinish_tr hp)
      intro x y h
      apply RootRS.mono h.1
      intro σ s hs
      refine ⟨hs.1.1,hs.1.2.resolve_left ?_⟩
      intro ht
      obtain ⟨σ',τ,_,_,_,_,hx,_⟩ := h.1.1
      have he := h.2
      change some (x.gpr .x9 != 0)=some true at he
      rw [hx.2,ht,Nat.mul_zero] at he
      cases he
      · intro _ _ _; trivial
    · have cf : positiveMaskChk p (p.ℓ-1)=true := by rcases hp with rfl|rfl <;> decide
      apply assocBack
      apply RelCT.mono (positiveMaskR_tr hP cf)
      · intro x y h
        exact ⟨h.1.1.mono (fun _ _ h=>h) (fun _ _ hs=>hs.1.1),h.1.2.1⟩
      · intro _ _ _; trivial

theorem masks_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : p=mlDsa65∨p=mlDsa87) {σ s : State} {t : Nat}
    (h : PositiveIL p S σ t s) (hm : t=0∨Mask p σ t s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Cached.masks P p) s (PositiveICm p S σ t p.ℓ) := by
  have hn : 2*(p.ℓ/2)=p.ℓ-1 := by rcases hp with rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Cached.masks
  refine WP.seq (WP.mono (prefix_ok hP hp h hm) fun u hu=>?_)
  rw [hn] at hu
  exact tailMask_ok hP hp hu.1 hu.2

theorem masks_tr {P : Prims} {S t : Nat} {E : State→State→Prop}
    (hP : PrimsOk P S) {p : Params} (hp : p=mlDsa65∨p=mlDsa87) :
    RelCT isa (RootRS p S E fun σ s=>PositiveIL p S σ t s ∧ (t=0∨Mask p σ t s))
      (Impl.MlDsa.AArch64.Sign.Cached.masks P p)
      (RootRS p S E (PositiveICm p S · t p.ℓ)) := by
  have hn : 2*(p.ℓ/2)=p.ℓ-1 := by rcases hp with rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Cached.masks
  have hf := prefix_tr (E:=E) (t:=t) hP hp
  rw [hn] at hf
  exact RelCT.seq hf (tailMask_tr hP hp)

end VG.Proof.MlDsa.AArch64.Sign.Cached
