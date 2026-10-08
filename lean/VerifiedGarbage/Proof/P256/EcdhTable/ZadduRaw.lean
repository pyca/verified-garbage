import VerifiedGarbage.Proof.P256.EcdhTable.RawField
import VerifiedGarbage.Proof.P256.EcdhJac.Zaddu

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem zaddu_raw_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k m : Nat} {s : State} (hP : onCurve C P=true)
    (hm2 : 2≤m) (hm15 : m≤15) (hf : Fixed base P k s)
    (hp : JPt base s selectedSlot (mul m P))
    (hl : ∀x∈[K.D.x,K.D.y],wordsVal s.mem base x 4<C.p)
    (hd : InvJ C (tmv C 4 base s K.D.x) (tmv C 4 base s K.D.y) (tmv C 4 base s K.E.z) P) :
    WP isa (.block (Impl.P256.EcdhJac.zadduOps.flatMap Impl.P256.VerifySparse.op)) s fun t =>
      Frame base work s t ∧ Fixed base P k t ∧ JPt base t selectedSlot (mul (m+1) P) ∧
      (∀x∈[K.D.x,K.D.y],wordsVal t.mem base x 4<C.p) ∧
      InvJ C (tmv C 4 base t K.D.x) (tmv C 4 base t K.D.y) (tmv C 4 base t K.E.z) P ∧ t.gpr .x19=s.gpr .x19 := by
  have hi : Inv M base 8192 C.p Sl [K.D.x,K.D.y,K.E.x,K.E.y,K.E.z,5400] (tmv C 4 base s) s := by
    refine ⟨hf.field.scr,hf.field.mod,by decide,?_,fun _ _ => rfl⟩
    intro x hx
    have hh : x=K.D.x∨x=K.D.y∨x=K.E.x∨x=K.E.y∨x=K.E.z∨x=5400 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx
    rcases hh with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hl _ (by decide)
    · exact hl _ (by decide)
    · exact hp.lt 0 (by decide)
    · exact hp.lt 1 (by decide)
    · exact hp.lt 2 (by decide)
    · exact hp.lt 3 (by decide)
  rw [zaddu_eq]
  refine WP.mono (table_raw_field (N:=zadduN) (by decide)
    (by decide : readsOk zadduN [0,1,8,9,10,11]=true) hi (by decide)) fun t ⟨kt,it,eqs⟩ => ?_
  have fr := tblFrame kt
  have vals := fun {i : Nat} (h : i∈zadduN.map FOp.out) => tbl_val it eqs h
  obtain ⟨ht,h11,h12⟩ := zadduN_run (fun j => tmv C 4 base s (tblσ j))
  generalize runOps zadduN (fun j => tmv C 4 base s (tblσ j))=r at vals ht h11 h12
  have h2 : tmv C 4 base s (tblσ 11)=tmv C 4 base s (tblσ 10)*tmv C 4 base s (tblσ 10) := hp.z2
  have jp : InvJ C (tmv C 4 base s K.P.x) (tmv C 4 base s K.P.y) 1 P := by
    have h := InvJ.of_rep01 hf.peer (Or.inl hf.one); rw [hf.one] at h; exact h
  have p0 : P≠.infinity := fun hh => hC.one_ne_zero ((jp.z_zero_iff hC).mpr hh)
  have hx := zaddu_x hC hO hP p0 (by decide) hm2 hm15 hd hp.jac hp.z
  obtain ⟨js,jd⟩ := InvJ.zaddu hC ha hP (hC.onCurve_mul hP m) hd hp.jac hp.z hx
  have hm : add (mul m P) P=mul (m+1) P := by
    calc
      add (mul m P) P=add (mul m P) (mul 1 P) := by rw [mul_one_pt]
      _=mul (m+1) P := hC.add_mul_mul hP m 1
  rw [hm] at js
  change ((r 8,r 9,r 10),(r 0,r 1))=zadduF _ _ _ _ _ at ht
  change InvJ C (zadduF (tmv C 4 base s (tblσ 0)) (tmv C 4 base s (tblσ 1))
    (tmv C 4 base s (tblσ 8)) (tmv C 4 base s (tblσ 9)) (tmv C 4 base s (tblσ 10))).1.1
    (zadduF (tmv C 4 base s (tblσ 0)) (tmv C 4 base s (tblσ 1))
    (tmv C 4 base s (tblσ 8)) (tmv C 4 base s (tblσ 9)) (tmv C 4 base s (tblσ 10))).1.2.1
    (zadduF (tmv C 4 base s (tblσ 0)) (tmv C 4 base s (tblσ 1))
    (tmv C 4 base s (tblσ 8)) (tmv C 4 base s (tblσ 9)) (tmv C 4 base s (tblσ 10))).1.2.2 _ at js
  have js' : InvJ C (r 8) (r 9) (r 10) (mul (m+1) P) := by
    have hh := congrArg (fun q : (Fe C × Fe C × Fe C) × (Fe C × Fe C) =>
      InvJ C q.1.1 q.1.2.1 q.1.2.2 (mul (m+1) P)) ht
    exact hh.mpr js
  have jd' : InvJ C (r 0) (r 1) (r 10) P := by
    have hh := congrArg (fun q : (Fe C × Fe C × Fe C) × (Fe C × Fe C) =>
      InvJ C q.2.1 q.2.2 q.1.2.2 P) ht
    exact hh.mpr jd
  have hz : r 10≠0 := fun hh => Window5.mul_ne_infinity hO hP p0 (by omega)
    (by
      have hn : 17≤C.n := by decide
      omega) ((js'.z_zero_iff hC).mp hh)
  have v0 := vals (i:=0) (by decide)
  have v1 := vals (i:=1) (by decide)
  have hv : ∀i<5,tmv C 4 base t (selectedSlot i)=r (8+i) ∧ wordsVal t.mem base (selectedSlot i) 4<C.p := by
    intro i hi
    have : i=0∨i=1∨i=2∨i=3∨i=4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl
    · exact vals (i:=8) (by decide)
    · exact vals (i:=9) (by decide)
    · exact vals (i:=10) (by decide)
    · exact vals (i:=11) (by decide)
    · exact vals (i:=12) (by decide)
  refine ⟨fr,hf.keep (frame_build fr),⟨fun i hi => (hv i hi).2,?_,?_,?_,?_⟩,?_,?_,kt.gpr _ (by decide)⟩
  · rw [(hv 0 (by decide)).1,(hv 1 (by decide)).1,(hv 2 (by decide)).1]; exact js'
  · rw [(hv 2 (by decide)).1]; exact hz
  · rw [(hv 3 (by decide)).1,(hv 2 (by decide)).1]; exact h11 h2
  · rw [(hv 4 (by decide)).1,(hv 3 (by decide)).1,(hv 2 (by decide)).1]; exact h12
  · intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact v0.2
    · rw [List.mem_singleton.mp hx]; exact v1.2
  · change InvJ C (tmv C 4 base t (tblσ 0)) (tmv C 4 base t (tblσ 1)) (tmv C 4 base t (tblσ 10)) P
    rw [v0.1,v1.1,(vals (i:=10) (by decide)).1]
    exact jd'

end VG.Proof.P256.EcdhJac
