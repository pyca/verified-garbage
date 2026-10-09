import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLane

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
