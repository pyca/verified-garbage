import VerifiedGarbage.Proof.Weierstrass.X86.NafTable
import VerifiedGarbage.Proof.Weierstrass.X86.NafDigitRead

/-! Stable table entries and scalar digits across the public multiplication loop. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def nafLive (K : WinCfg) : List Nat := nafTableLive K 8

structure NafStable (K : WinCfg) (C : Curve) (base : Addr)
    (P : Point C) (β : Nat → BitVec 8) (s : State) : Prop where
  zero : wordsVal s.mem base K.zero K.M.n=0
  table : ∀ a,1≤a → a≤8 → InvJ C (tmv C K.M.n base s (K.tblPt a).x)
    (tmv C K.M.n base s (K.tblPt a).y) (tmv C K.M.n base s (K.tblPt a).z) (mul (2*a-1) P)
  bits : ∀ i<257,s.mem (off base (K.bits+i))=β i

theorem nafLive_R (K : WinCfg) : ∀ x∈jacCoords K.R,x∈nafLive K := by
  intro x hx
  simp only [nafLive,nafTableLive,List.mem_append]
  grind

theorem nafOther_slots (K : WinCfg) : ∀ x∈winOther K,x∈nafSlots K :=
  fun _ hx => List.mem_append_left _ (List.mem_append_right _ hx)

theorem nafRo_slots (K : WinCfg) : ∀ x∈winRo K,x∈nafSlots K :=
  fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)

theorem NafStable.keep {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    {P : Point C} {β : Nat → BitVec 8} {s t : State}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hs : Scr s base size)
    (h : NafStable K C base P β s) (hk : ProgKeep K.M base wk (winOther K) s t) :
    NafStable K C base P β t := by
  have hn := hs.nowrap
  refine ⟨?_,fun a ha h8 => ?_,fun i hi => ?_⟩
  · rw [hk.slot hL.lay hAcc hs (nafOther_slots K)
      (nafRo_slots K _ (by simp [winRo])) (hL.ro _ (by simp [winRo])),h.zero]
  · have hv (x : Nat) (hx : x∈jacCoords (K.tblPt a)) :
        tmv C K.M.n base t x=tmv C K.M.n base s x := by
      unfold tmv
      rw [hk.slot hL.lay hAcc hs (nafOther_slots K) (nafTblPt_mem K hL.n ha (by omega) x hx) ?_]
      intro ho
      have sep := hL.tbl x (List.mem_append_right _ ho)
      simp only [jacCoords,WinCfg.tblPt,hL.n,List.mem_cons,List.not_mem_nil,or_false] at hx
      omega
    rw [hv _ (by simp [jacCoords]),hv _ (by simp [jacCoords]),hv _ (by simp [jacCoords])]
    exact h.table a ha h8
  · rw [hk.unch.byte (fun w hw => ?_) (by have := hL.bits; omega),h.bits i hi]
    simp only [progW,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl | rfl | rfl
    · have hb := hL.bits_w x (List.mem_append_left _ hx)
      dsimp only; rw [hL.n]; omega
    · have hb := hL.bits_tmp
      dsimp only; rw [hL.n]; omega
    · dsimp only; omega
    · have := hL.bits; have := hL.size_le
      dsimp only [Mont.outW]; omega

structure NafCore (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (P : Point C) (β : Nat → BitVec 8) (e : Nat) (s : State) : Prop where
  field : Inv K.M base size C.p (·∈nafSlots K) (nafLive K) (tmv C K.M.n base s) s
  stable : NafStable K C base P β s
  point : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul e P)

theorem NafCore.next {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    {P : Point C} {β : Nat → BitVec 8} {e e' : Nat} {s t : State}
    (hL : NafLay K size) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K)) (hBitsWk : K.bits+260≤wk)
    (h : NafCore K C base size P β e s) {E : Nat → Fe C}
    (hk : ProgKeep K.M base wk (winOther K) s t)
    (hi : Inv K.M base size C.p (·∈nafSlots K) (nafLive K) E t)
    (hp : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul e' P)) :
    NafCore K C base size P β e' t :=
  ⟨hi.to_tmv,h.stable.keep hL hAcc hBitsWk h.field.scr hk,hi.point_tmv (nafLive_R K) hp⟩

theorem NafCore.of_keeps {K : WinCfg} {C : Curve} {base : Addr} {size e : Nat}
    {β : Nat → BitVec 8} {P : Point C} {s t : State} {rs : List Reg}
    (h : NafCore K C base size P β e s) (hk : CKeeps rs s t) (h0 : Reg.edi∉rs) (hsp : Reg.esp∉rs := by decide) :
    NafCore K C base size P β e t := by
  have hm : tmv C K.M.n base t=tmv C K.M.n base s := by
    funext x; unfold tmv; rw [hk.2.1]
  refine ⟨?_,?_,?_⟩
  · rw [hm]; exact h.field.of_keeps hk h0 hsp
  · refine ⟨?_,fun a ha h8 => ?_,fun i hi => ?_⟩
    · rw [hk.2.1]; exact h.stable.zero
    · rw [hm]; exact h.stable.table a ha h8
    · rw [hk.2.1]; exact h.stable.bits i hi
  · rw [hm]; exact h.point

end VG.Proof.Weierstrass.X86
