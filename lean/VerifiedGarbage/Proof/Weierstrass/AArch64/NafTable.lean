import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableStep
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- Build the eight odd multiples and the cached double. -/
theorem nafTable_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C)
    (ht : K.tbl<4096) (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    {s : State} (hI : Inv K.M base size C.p (·∈jacWinSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (Naf.table K) s (fun t => NafTableInv K C base size P s t 8) := by
  unfold Naf.table
  apply WP.assoc
  refine WP.seq (WP.mono (nafTable_init_ok hL hJ hAl hm hC ha ht hP hI hJP) fun a ia => ?_)
  apply countLoop_ok (Inv := fun j t => NafTableInv K C base size P s t (8-j))
    (n := 7) (by decide)
  · intro j u hj hj7 hu
    refine WP.mono (nafTable_step_ok hL hJ hAl hm hC ha hOne hP (by omega) (by omega) hu)
      fun t it => ?_
    have he : 8-j+1=8-(j-1) := by omega
    refine ⟨he ▸ it,?_⟩
    have hc := it.counter
    have he' : 8-(8-j+1)=j-1 := by omega
    rwa [he'] at hc
  · intro t it; exact it
  · decide
  · exact ia

theorem nafTableLive_full (K : WinCfg) : ∀ x∈nafLive K, x∈nafTableLive K 8 := by
  intro x hx
  simp only [nafLive,List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx)))
  · simp only [nafTableLive,jacCoords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    by_cases h : i<24
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_range.mpr h,rfl⟩)
    · have hb : K.tbl+32*i ∈ jacCoords (Naf.twice K) := by
        simp only [jacCoords,Naf.twice,Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false]
        omega
      exact List.mem_append_left _ (List.mem_append_right _ hb)

/-- Table construction preserves all 257 signed digits. -/
theorem NafTableInv.ready {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    {P : Point C} {β : Nat → BitVec 8} {s t : State} (hL : JacWinLay K size)
    (hI : NafTableInv K C base size P s t 8)
    (hz : wordsVal s.mem base K.zero K.M.n=0)
    (hb : ∀ i<257, s.mem (off base (K.bits+i))=β i) :
    Inv K.M base size C.p (·∈jacWinSlots K) (nafLive K) (tmv C K.M.n base t) t ∧
      NafStable K C base P β t := by
  refine ⟨hI.field.sub (nafTableLive_full K),?_,hI.table,?_⟩
  · rw [jacTree_ro_words hL hI.unch hI.field.scr.nowrap (by simp [winRo]),hz]
  · intro i hi
    rw [hI.unch.byte (fun w hw => ?_) (by have := hL.bits; have := hI.field.scr.nowrap; omega),hb i hi]
    simp only [jacTreeWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨x,hx,rfl⟩ | rfl
    · have hb' := hL.bits_w x hx
      dsimp only; rw [hL.n]; omega
    · have hb' := hL.bits_tmp
      dsimp only; rw [hL.n]; omega

end VG.Proof.Weierstrass.AArch64
