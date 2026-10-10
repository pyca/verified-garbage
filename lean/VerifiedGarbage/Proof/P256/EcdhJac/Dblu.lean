import VerifiedGarbage.Proof.P256.EcdhJac.TableMath
import VerifiedGarbage.Proof.P256.EcdhJac.DbluCertificate
import VerifiedGarbage.Proof.P256.EcdhJac.ZadduCertificate
import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.P256.EcdhJac.BuildState

/-! ## `TableField` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

 theorem table_field {N : List FOp}
    (cert : FieldCase (N.map (FOp.rename tblσ))) (hout : ∀op∈N,op.out<13)
    {Rd : List Nat} (hreads : readsOk N Rd=true)
    {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl V E s) (hv : ∀i∈Rd,tblσ i∈V) :
    WP isa (Impl.P256.EcdhJac.arithmetic (N.map (FOp.rename tblσ))) s fun t =>
      ProgKeep M base tblW s t ∧
      Inv M base 8192 C.p Sl (validAfter (N.map (FOp.rename tblσ)) V)
        (runOps (N.map (FOp.rename tblσ)) E) t ∧
      ∀i,runOps (N.map (FOp.rename tblσ)) E (tblσ i)=runOps N (fun j => E (tblσ j)) i := by
  have nd : tblW.Nodup := by decide
  have hp : ∀x∈[K.P.x,K.P.y,K.P.z],x∉tblW := by decide
  have inj : ∀op∈N,∀y,tblσ y=tblσ op.out→y=op.out := fun op hop y =>
    getD_append_inj nd hp (hp _ (by simp)) (by simpa [tblW] using hout op hop) y
  have hs : ∀i,Sl (tblσ i) := fun i =>
    (show ∀x∈tblW++[K.P.x,K.P.y,K.P.z],Sl x from by decide +kernel) _
      (getD_append_mem (by simp) i)
  have hsops : ∀op∈N.map (FOp.rename tblσ),∀x∈op.out::op.ins,Sl x := by
    intro op hop
    obtain ⟨op,_,rfl⟩ := List.mem_map.mp hop
    cases op <;> simp only [FOp.rename,FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] <;>
      rintro x (rfl|rfl|rfl) <;> exact hs _
  have hlo : ∀op∈N.map (FOp.rename tblσ),Low M (op.out::op.ins) := by
    intro op _
    exact Low.small (by decide) _
  refine WP.mono (field_ok cert layout aligned (unitMod_pow_two (by decide) _) hi hsops hlo
    (readsOk_mono (readsOk_rename tblσ hreads) (by
      intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact hv i hi))) fun t ⟨kt,it⟩ =>
      ⟨kt.mono ?_,it,fun i => congrFun (runOps_rename tblσ N E inj) i⟩
  intro x hx
  obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hx
  obtain ⟨op,hopN,rfl⟩ := List.mem_map.mp hop
  rw [FOp.out_rename]
  unfold tblσ
  rw [getD_append_left (by simpa [tblW] using hout op hopN)]
  exact List.getElem_mem _

end VG.Proof.P256.EcdhJac

end

/-! ## `Dblu` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

 theorem tbl_val {N : List FOp} {base : Addr} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl (validAfter (N.map (FOp.rename tblσ)) V)
      (runOps (N.map (FOp.rename tblσ)) E) s)
    (he : ∀i,runOps (N.map (FOp.rename tblσ)) E (tblσ i)=runOps N (fun j => E (tblσ j)) i)
    {i : Nat} (ho : i∈N.map FOp.out) :
    tmv C 4 base s (tblσ i)=runOps N (fun j => E (tblσ j)) i ∧ wordsVal s.mem base (tblσ i) 4<C.p := by
  have hv : tblσ i∈validAfter (N.map (FOp.rename tblσ)) V := by
    rw [mem_validAfter]
    right
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp ho
    exact List.mem_map.mpr ⟨FOp.rename tblσ op,List.mem_map_of_mem hop,FOp.out_rename ..⟩
  exact ⟨(hi.val _ hv).trans (he i),hi.lt _ hv⟩

 theorem tblFrame {base : Addr} {s t : State} (hk : ProgKeep M base tblW s t) : Frame base work s t :=
  AllocatedFrame.of_prog hk clob_regs (by decide +kernel)

 theorem dblu_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} {s : State} (hP : onCurve C P=true)
    (hf : Fixed base P k s) :
    WP isa (Impl.P256.EcdhJac.arithmetic Impl.P256.EcdhJac.dbluOps) s fun t =>
      Frame base work s t ∧ Fixed base P k t ∧
      JPt base t selectedSlot (mul 2 P) ∧
      InvJ C (tmv C 4 base t K.S.t3) (tmv C 4 base t K.S.t2) (tmv C 4 base t K.E.z) P ∧
      wordsVal t.mem base K.S.t3 4<C.p ∧ wordsVal t.mem base K.S.t2 4<C.p := by
  rw [dblu_eq]
  refine WP.mono (table_field (N:=dbluN) Dblu.caseProof (by decide) (by decide : readsOk dbluN [13,14,15]=true)
    hf.field (by decide)) fun t ⟨kt,it,eqs⟩ => ?_
  have fr := tblFrame kt
  have vals := fun {i : Nat} (h : i∈dbluN.map FOp.out) => tbl_val it eqs h
  have h15 : tmv C 4 base s (tblσ 15)=1 := hf.one
  obtain ⟨hT,h11,h12,h5,h4⟩ := dbluN_run (fun j => tmv C 4 base s (tblσ j)) h15
  generalize runOps dbluN (fun j => tmv C 4 base s (tblσ j))=r at vals hT h11 h12 h5 h4
  have jp : InvJ C (tmv C 4 base s (tblσ 13)) (tmv C 4 base s (tblσ 14)) 1 P := by
    have h := InvJ.of_rep01 hf.peer (Or.inl hf.one)
    rw [hf.one] at h
    exact h
  have j2 := InvJ.dbl' hC ha hP jp hT
  have pp : add P P=mul 2 P := by
    rw [show add P P=add (mul 1 P) (mul 1 P) by rw [mul_one_pt],hC.add_mul_mul hP]
  rw [pp] at j2
  have p0 : P≠.infinity := fun hh => hC.one_ne_zero ((jp.z_zero_iff hC).mpr hh)
  have hz : r 10≠0 := fun h => Window5.mul_ne_infinity hO hP p0 (by decide) (by decide)
    ((j2.z_zero_iff hC).mp h)
  have jd : InvJ C (r 5) (r 4) (r 10) P :=
    jp.rescale hC hz hC.one_ne_zero h5 h4 (by grind only)
  have v4 := vals (i:=4) (by decide)
  have v5 := vals (i:=5) (by decide)
  have v8 := vals (i:=8) (by decide)
  have v9 := vals (i:=9) (by decide)
  have v10 := vals (i:=10) (by decide)
  have v11 := vals (i:=11) (by decide)
  have v12 := vals (i:=12) (by decide)
  have hv : ∀i<5,tmv C 4 base t (selectedSlot i)=r (8+i) ∧
      wordsVal t.mem base (selectedSlot i) 4<C.p := by
    intro i hi
    have : i=0∨i=1∨i=2∨i=3∨i=4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl
    · exact v8
    · exact v9
    · exact v10
    · exact v11
    · exact v12
  refine ⟨fr,hf.keep (frame_build fr),⟨fun i hi => (hv i hi).2,?_,?_,?_,?_⟩,?_,v5.2,v4.2⟩
  · rw [(hv 0 (by decide)).1,(hv 1 (by decide)).1,(hv 2 (by decide)).1]; exact j2
  · rw [(hv 2 (by decide)).1]; exact hz
  · rw [(hv 3 (by decide)).1,(hv 2 (by decide)).1]; exact h11
  · rw [(hv 4 (by decide)).1,(hv 3 (by decide)).1,(hv 2 (by decide)).1]; exact h12
  · change InvJ C (tmv C 4 base t (tblσ 5)) (tmv C 4 base t (tblσ 4)) (tmv C 4 base t (tblσ 10)) P
    rw [v5.1,v4.1,v10.1]
    exact jd

end VG.Proof.P256.EcdhJac

end
