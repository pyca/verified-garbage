import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
import VerifiedGarbage.Proof.MlKem.AArch64.Vec

/-! ## From `ResidentRejStore.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq coeffAt)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Proof.MlDsa.AArch64.Arith.Neon (coeffAt_write16)

/-- A vector store appends four accepted coefficients without touching an
already accepted prefix. -/
theorem stored_append_four {m : Mem} {p : Addr} {L W : List Zq} {v : BitVec 128}
    (hL : Stored m p L) (hsize : L.length+4≤256) (hlen : W.length=4)
    (hv : ∀e<4,(vword v e).toNat=(W.getD e 0).val) :
    Stored (m.write (coeffAddr p L.length) 16 v) p (L++W) := by
  intro i hi
  have hb : i<256 := by rw [List.length_append,hlen] at hi; omega
  rw [coeffAt_write16 _ _ hsize _ hb]
  by_cases h : i<L.length
  · rw [ite_eq_right (by omega),List.getD_eq_getElem?_getD,List.getElem?_append_left h]
    exact hL i h
  · rw [ite_eq_left (by rw [List.length_append,hlen] at hi; omega),
      List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [zw_toNat]
    exact hv (i-L.length) (by rw [List.length_append,hlen] at hi; omega)

/-- Successful vector acceptance stores all four values in one write and
advances exactly as four scalar acceptances would. -/
theorem vectorAccept_ok {s : State} {p : Addr} {L W : List Zq}
    (hL : Stored s.mem p L) (hsize : L.length+4≤256) (hlen : W.length=4)
    (hv : ∀e<4,(vword (s.v .v1) e).toNat=(W.getD e 0).val)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length)
    (hw : InRegions s.wr (s.gpr .x3) 16) :
    WP isa (.block vectorAccept) s fun t =>
      Keep [.x3,.x4] s t ∧ Frame [polyR p] s.mem t.mem ∧
      t.mem=s.mem.write (s.gpr .x3) 16 (s.v .v1) ∧
      t.gpr .x3=coeffAddr p (L++W).length ∧
      (t.gpr .x4).toNat=256-(L++W).length ∧ Stored t.mem p (L++W) := by
  refine wp_strq (a := s.gpr .x3) (by decide) (ptr_zero _) hw fun a ha =>
    wp_addImm (by decide) fun b hb eb => wp_subImm (by decide) fun t ht et => wp_nil ?_
  have hm : t.mem=s.mem.write (s.gpr .x3) 16 (s.v .v1) := by rw [ht.mem,hb.mem,ha.mem]
  refine ⟨((ha.keep.trans hb.keep).trans ht.keep).mono (by decide),?_,hm,?_,?_,?_⟩
  · rw [hm,h3]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _
      (Offset.contains_base p (by omega) (by omega))
  · rw [ht.get .x3,eb,ha.gpr,h3,List.length_append,hlen,coeffAddr,coeffAddr]
    rw [Offset.add_add]
    congr 1
  · rw [et,hb.get .x4,ha.gpr,toNat_sub_c _ 4 (by decide),h4,List.length_append,hlen,
      ite_eq_left (by omega)]
    omega
  · rw [hm,h3]
    exact stored_append_four hL hsize hlen hv

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejLane.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (acc accept_ok)
open VG.Spec.MlDsa (Zq q)

/-- Scalar fallback on one already gathered lane. The selected lane is
zero-extended, and every vector (including unprocessed lanes) is preserved. -/
theorem lane_ok {s : State} {r : VReg} {e : Nat} {p : Addr} {L : List Zq}
    (he : e<4) (hz : (vword (s.v r) e).toNat<2^23)
    (h9 : (s.gpr .x9).toNat=q) (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length<256)
    (hst : Stored s.mem p L) (hw : InRegions s.wr (coeffAddr p L.length) 4) :
    WP isa (.block (.umov .w .x11 r e :: rnAccept)) s fun t =>
      Keep [.x11,.x3,.x4,.x13,.x14,.x15] s t ∧ t.v=s.v ∧
      Frame [polyR p] s.mem t.mem ∧
      t.gpr .x3=coeffAddr p (acc L (vword (s.v r) e).toNat).length ∧
      (t.gpr .x4).toNat=256-(acc L (vword (s.v r) e).toNat).length ∧
      Stored t.mem p (acc L (vword (s.v r) e).toNat) := by
  have h : WP isa (.block (.umov .w .x11 r e :: rnAccept)) s fun t =>
      Keep [.x11,.x3,.x4,.x13,.x14,.x15] s t ∧
      Frame [polyR p] s.mem t.mem ∧
      t.gpr .x3=coeffAddr p (acc L (vword (s.v r) e).toNat).length ∧
      (t.gpr .x4).toNat=256-(acc L (vword (s.v r) e).toNat).length ∧
      Stored t.mem p (acc L (vword (s.v r) e).toNat) := by
    refine wp_x (d := .x11) (v := (vword (s.v r) e).setWidth 64)
      (by simp only [exec,Size.bits,show e*32<128 by omega,ite_true]; rfl) fun a ha ea => ?_
    refine WP.mono (accept_ok (aP := p) (L := L) (z := (vword (s.v r) e).toNat)
      (by rw [ea,BitVec.toNat_setWidth_of_le (by decide)]) hz
      (by rw [ha.get .x9]; exact h9) (by rw [ha.get .x3]; exact h3)
      (by rw [ha.get .x4]; exact h4) hL (by rw [ha.mem]; exact hst)
      (by rw [ha.wr]; exact hw)) fun t ⟨hk,hf,hp,hcount,hstored⟩ => ?_
    exact ⟨(ha.keep.trans hk).mono (by decide),by rw [←ha.mem]; exact hf,hp,hcount,hstored⟩
  refine WP.mono (WP.keepV (by rfl) h) ?_
  rintro t ⟨⟨hk,hf,hp,hcount,hstored⟩,hv⟩
  exact ⟨hk,hv,hf,hp,hcount,hstored⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejFallback.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (acc acc_length)
open VG.Spec.MlDsa (Zq q)

def laneFold (v : VReg → BitVec 128) : List (VReg×Nat) → List Zq → List Zq
 | [], L => L
 | (r,e)::rs, L => laneFold v rs (acc L (vword (v r) e).toNat)

theorem laneFold_length (v : VReg → BitVec 128) (rs : List (VReg×Nat)) (L : List Zq) :
    L.length≤(laneFold v rs L).length ∧ (laneFold v rs L).length≤L.length+rs.length := by
  induction rs generalizing L with
  | nil => exact ⟨Nat.le_refl _,by simp [laneFold]⟩
  | cons re rs ih =>
    rcases re with ⟨r,e⟩
    have hh := ih (acc L (vword (v r) e).toNat)
    have ha : L.length≤(acc L (vword (v r) e).toNat).length ∧
        (acc L (vword (v r) e).toNat).length≤L.length+1 := by
      rw [acc_length]
      split <;> omega
    change L.length≤(laneFold v rs (acc L (vword (v r) e).toNat)).length ∧
      (laneFold v rs (acc L (vword (v r) e).toNat)).length≤L.length+(rs.length+1)
    omega

/-- On the all-accepted branch the fallback's logical result is an append,
which is exactly the result written by the vector store. -/
theorem laneFold_all {v : VReg → BitVec 128} (rs : List (VReg×Nat)) (L : List Zq)
    (h : ∀r e,(r,e)∈rs → (vword (v r) e).toNat<q) :
    laneFold v rs L=L++rs.map (fun (r,e) => Fin.ofNat q (vword (v r) e).toNat) := by
  induction rs generalizing L with
  | nil => simp only [laneFold,List.map_nil,List.append_nil]
  | cons re rs ih =>
    rcases re with ⟨r,e⟩
    rw [laneFold,acc,ite_eq_left (h r e List.mem_cons_self),
      ih _ (fun r' e' hm => h r' e' (List.mem_cons_of_mem _ hm))]
    simp only [List.map_cons,List.append_assoc,List.singleton_append]

def lanesCode (rs : List (VReg×Nat)) : List Instr :=
 rs.flatMap fun (r,e) => .umov .w .x11 r e :: rnAccept

abbrev fallbackRegs : List Reg := [.x11,.x3,.x4,.x13,.x14,.x15]

/-- Fixed-size scalar fallback is ordered identically to the source byte
stream, even when any subset of candidates is rejected. -/
theorem lanes_ok (rs : List (VReg×Nat)) {s : State} {p : Addr} {L : List Zq}
    (hr : ∀r e,(r,e)∈rs → e<4 ∧ (vword (s.v r) e).toNat<2^23)
    (h9 : (s.gpr .x9).toNat=q) (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length+rs.length≤256)
    (hst : Stored s.mem p L) (hw : ∀i<256,InRegions s.wr (coeffAddr p i) 4) :
    WP isa (.block (lanesCode rs)) s fun t =>
      Keep fallbackRegs s t ∧ t.v=s.v ∧ Frame [polyR p] s.mem t.mem ∧
      t.gpr .x3=coeffAddr p (laneFold s.v rs L).length ∧
      (t.gpr .x4).toNat=256-(laneFold s.v rs L).length ∧
      Stored t.mem p (laneFold s.v rs L) := by
  induction rs generalizing s L with
  | nil =>
    exact WP.block_nil_iff.mpr ⟨Keep.refl _ _,rfl,Frame.refl _ _,h3,h4,hst⟩
  | cons re rs ih =>
    rcases re with ⟨r,e⟩
    have hb := hr r e (List.mem_cons_self)
    have hl : L.length<256 := by simp only [List.length_cons] at hL; omega
    have hnext : (acc L (vword (s.v r) e).toNat).length+rs.length≤256 := by
      rw [acc_length]
      simp only [List.length_cons] at hL
      split <;> omega
    rw [lanesCode,List.flatMap_cons,WP.block_append_iff]
    refine WP.mono (lane_ok hb.1 hb.2 h9 h3 h4 hl hst (hw _ hl))
      fun a ⟨ha,hvec,hframe,hptr,hcount,hstored⟩ => ?_
    refine WP.mono (ih (s := a) (L := acc L (vword (s.v r) e).toNat)
      (fun r' e' hm => by rw [hvec]; exact hr r' e' (List.mem_cons_of_mem _ hm))
      (by rw [ha.get .x9]; exact h9) hptr hcount hnext hstored
      (fun i hi => by rw [ha.wr]; exact hw i hi)) fun t ⟨ht,hvec',hf,hp,hc,hs⟩ => ?_
    rw [hvec] at hp hc hs
    exact ⟨(ha.trans ht).mono (by simp [fallbackRegs]),hvec'.trans hvec,hframe.trans hf,hp,hc,hs⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejChoice.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def fourLanes : List (VReg×Nat) := [(.v1,0),(.v1,1),(.v1,2),(.v1,3)]

def fourValues (v : BitVec 128) : List Zq :=
 [Fin.ofNat q (vword v 0).toNat,Fin.ofNat q (vword v 1).toNat,
  Fin.ofNat q (vword v 2).toNat,Fin.ofNat q (vword v 3).toNat]

theorem fourLanes_all {s : State} {L : List Zq}
    (h : ∀e<4,(vword (s.v .v1) e).toNat<q) :
    laneFold s.v fourLanes L=L++fourValues (s.v .v1) := by
  rw [laneFold_all _ _ (by
    intro r e hr
    simp only [fourLanes,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hr
    rcases hr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact h _ (by decide))]
  rfl

def ChoicePost (s : State) (p : Addr) (L : List Zq) (t : State) : Prop :=
 Keep fallbackRegs s t ∧ t.v=s.v ∧ Frame [polyR p] s.mem t.mem ∧
 t.gpr .x3=coeffAddr p (laneFold s.v fourLanes L).length ∧
 (t.gpr .x4).toNat=256-(laneFold s.v fourLanes L).length ∧
 Stored t.mem p (laneFold s.v fourLanes L)

/-- The vector fast store and ordered scalar fallback have the same logical
result. No assumption about which candidates are accepted is imposed. -/
theorem fourChoice_ok {s : State} {p : Addr} {L : List Zq}
    (hz : ∀e<4,(vword (s.v .v1) e).toNat<2^23)
    (hf : s.gpr .x6=0 ↔ ∀e<4,(vword (s.v .v1) e).toNat<q)
    (h9 : (s.gpr .x9).toNat=q) (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length+4≤256)
    (hst : Stored s.mem p L)
    (hw : ∀i<256,InRegions s.wr (coeffAddr p i) 4)
    (hw16 : InRegions s.wr (s.gpr .x3) 16) :
    WP isa (.ite (.zero .x .x6) (.block vectorAccept) (.block vectorReject)) s
      (ChoicePost s p L) := by
  by_cases he : s.gpr .x6=0
  · have ha := hf.mp he
    refine WP.ite true (by rw [eval_zero,he]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h)
    have hv (e : Nat) (he' : e<4) :
        (vword (s.v .v1) e).toNat=((fourValues (s.v .v1)).getD e 0).val := by
      have hh := ha e he'
      rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl
      all_goals exact (Nat.mod_eq_of_lt hh).symm
    refine WP.mono (WP.keepV (by decide) (vectorAccept_ok hst hL (by rfl) hv h3 h4 hw16))
      fun t ⟨⟨hk,hframe,_,hp,hcount,hs⟩,hvec⟩ => ?_
    unfold ChoicePost
    rw [fourLanes_all ha]
    exact ⟨hk.mono (by decide),hvec,hframe,hp,hcount,hs⟩
  · refine WP.ite false (by rw [eval_zero,show (s.gpr .x6 == 0)=false from beq_eq_false_iff_ne.mpr he])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    have hcode : vectorReject=lanesCode fourLanes := rfl
    rw [hcode]
    refine WP.mono (lanes_ok fourLanes (s := s) (p := p) (L := L) (by
      intro r e hr
      simp only [fourLanes,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hr
      rcases hr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      all_goals exact ⟨by decide,hz _ (by decide)⟩) h9 h3 h4 hL hst hw)
      fun t ⟨hk,hvec,hframe,hp,hcount,hs⟩ => ⟨hk,hvec,hframe,hp,hcount,hs⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
