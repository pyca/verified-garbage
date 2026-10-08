import VerifiedGarbage.Proof.P256.EcdhJac.Masks
import VerifiedGarbage.Proof.P256.EcdhJac.AddState

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem Fixed.peer_ne (hC : Law C) {base : Addr} {P : Point C} {k : Nat} {s : State}
    (h : Fixed base P k s) : P≠.infinity := by
  intro he
  have hp := h.peer
  rw [he] at hp
  exact hC.one_ne_zero (h.one.symm.trans hp.2.2)

theorem masked_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P Q : Point C} {k j : Nat} (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hq : k<C.n→Q=mul (32*Window5.winE (k+offset) 52 (j+1)) P)
    {s : State} (hs : RState base P Q k s) (hj : j<52)
    (h19 : s.gpr .x19=BitVec.ofNat 64 j)
    (hi : Inv M base 8192 C.p Sl addLive (tmv C 4 base s) s)
    (he : 1≤digitMagnitude k j→
      InvJ C (tmv C 4 base s K.E.x) (tmv C 4 base s K.E.y) (tmv C 4 base s K.E.z)
        (Window5.winPt C P (k+offset) j) ∧ tmv C 4 base s K.E.z≠0)
    (hd : (tmv C 4 base s K.D.x,tmv C 4 base s K.D.y,tmv C 4 base s K.D.z)=
      jacAddF (tmv C 4 base s K.R.x) (tmv C 4 base s K.R.y) (tmv C 4 base s K.R.z)
        (tmv C 4 base s K.E.x) (tmv C 4 base s K.E.y) (tmv C 4 base s K.E.z)) :
    WP isa (.block maskCode) s fun t => Frame base work s t ∧ LoopInv base P k j t := by
  have hq' : k<C.n→Q=mul (32*Window5.winE (k+16*Window5.geom 52) 52 (j+1)) P := by
    simpa only [offset_eq] using hq
  have he' : 1≤magH 16 (Window5.nib (k+16*Window5.geom 52) j)→
      InvJ C (tmv C 4 base s K.E.x) (tmv C 4 base s K.E.y) (tmv C 4 base s K.E.z)
        (Window5.winPt C P (k+16*Window5.geom 52) j) ∧ tmv C 4 base s K.E.z≠0 := by
    simpa only [digitMagnitude,offset_eq] using he
  obtain ⟨Q',hQ',hq',hj'⟩ := Window5.jstep_pt hC ha hO hP (hs.fixed.peer_ne hC)
    (by decide) (by decide) hj hQ hq' hs.point he'
  rw [←offset_eq] at hq' hj'
  refine WP.mono (masks_ok hs.fixed hj h19) fun t ⟨kt,hv⟩ => ?_
  have fw := kt.widenRegs allocated_regs
  have fixed := hs.fixed.keep (frame_build fw)
  have hziff : wordsVal s.mem base 576 4=0 ↔ tmv C 4 base s 576=0 :=
    (toM_eq_zero_iff (unitMod_pow_two (by decide) _) (hi.lt _ (by decide))).symm
  have values : ∀ i<3,tmv C 4 base t (512+32*i)=
      if digitMagnitude k j=0 then tmv C 4 base s (512+32*i)
      else if tmv C 4 base s 576=0 then tmv C 4 base s (704+32*i)
      else tmv C 4 base s (608+32*i) := by
    intro i hi'
    unfold tmv
    rw [hv i hi']
    split
    · rfl
    · rw [if_congr hziff rfl rfl]
      split <;> rfl
  have ilt : ∀ x∈live,wordsVal t.mem base x 4<C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx|hx
    · have hh : ∀ x∈[K.R.x,K.R.y,K.R.z],∃ i<3,x=512+32*i := by decide
      obtain ⟨i,hi',rfl⟩ := hh x hx
      rw [hv i hi']
      split
      · exact hi.lt _ (by
          have hh : ∀ i<3,512+32*i∈addLive := by decide
          exact hh i hi')
      · split
        · exact hi.lt _ (by
            have hh : ∀ i<3,704+32*i∈addLive := by decide
            exact hh i hi')
        · exact hi.lt _ (by
            have hh : ∀ i<3,608+32*i∈addLive := by decide
            exact hh i hi')
    · exact fixed.field.lt x hx
  have it : Inv M base 8192 C.p Sl live (tmv C 4 base t) t :=
    ⟨fixed.field.scr,fixed.field.mod,by decide,ilt,fun _ _ => rfl⟩
  refine ⟨fw,⟨⟨Q',hQ',hq',fixed,hs.table.keep fw,it,?_⟩,
    (kt.regs.gpr _ allocatedRegs_x19).trans h19⟩⟩
  have v0 := values 0 (by decide)
  have v1 := values 1 (by decide)
  have v2 := values 2 (by decide)
  change tmv C 4 base t K.R.x=_ at v0
  change tmv C 4 base t K.R.y=_ at v1
  change tmv C 4 base t K.R.z=_ at v2
  rw [v0,v1,v2]
  have dx := congrArg Prod.fst hd
  have dy := congrArg (fun p => p.2.1) hd
  have dz := congrArg (fun p => p.2.2) hd
  dsimp only at dx dy dz
  change InvJ C (if digitMagnitude k j=0 then tmv C 4 base s K.R.x else
      if tmv C 4 base s K.R.z=0 then tmv C 4 base s K.E.x else tmv C 4 base s K.D.x)
    (if digitMagnitude k j=0 then tmv C 4 base s K.R.y else
      if tmv C 4 base s K.R.z=0 then tmv C 4 base s K.E.y else tmv C 4 base s K.D.y)
    (if digitMagnitude k j=0 then tmv C 4 base s K.R.z else
      if tmv C 4 base s K.R.z=0 then tmv C 4 base s K.E.z else tmv C 4 base s K.D.z) Q'
  rw [dx,dy,dz]
  exact hj'

end VG.Proof.P256.EcdhJac
