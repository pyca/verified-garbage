import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideChoice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideValue

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (acc)
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def candidateFold (m : Mem) (p : Addr) (n : Nat) (L : List Zq) : List Zq :=
 ((List.range n).map (fun j => candidate m (p+BitVec.ofNat 64 (3*j)))).foldl acc L

theorem laneFold_map (v : VReg → BitVec 128) (rs : List (VReg×Nat)) (L : List Zq) :
    laneFold v rs L=(rs.map fun (r,e) => (vword (v r) e).toNat).foldl acc L := by
  induction rs generalizing L with
  | nil => rfl
  | cons re rs ih => exact ih _

/-- The wide probe consumes sixteen consecutive candidates with precisely
the scalar acceptance order, including every rejected candidate. -/
theorem wideStep_ok {s : State} {p : Addr} {L : List Zq}
    (hc : Constants s)
    (hr : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (12*j)) 16)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length+16≤256)
    (hst : Stored s.mem p L)
    (hw : ∀i<256,InRegions s.wr (coeffAddr p i) 4)
    (hw16 : ∀j<4,InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.seq (.block wideTry)
      (.ite (.zero .x .x6) (.block wideAccept) (.block wideReject))) s fun t =>
      Keep (([.x6,.x7] : List Reg)++fallbackRegs) s t ∧
      Frame [polyR p] s.mem t.mem ∧ Constants t ∧
      t.gpr .x3=coeffAddr p (candidateFold s.mem (s.gpr .x2) 16 L).length ∧
      (t.gpr .x4).toNat=256-(candidateFold s.mem (s.gpr .x2) 16 L).length ∧
      Stored t.mem p (candidateFold s.mem (s.gpr .x2) 16 L) := by
  refine WP.seq (WP.mono (wideTry_ok hc.index hr) fun a ⟨ha,hv,hflag⟩ => ?_)
  have hval (j : Nat) (hj : j<4) (e : Nat) (he : e<4) :
      (vword (a.v wideRegs[j]!) e).toNat=
        candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (12*j+3*e)) := by
    rw [hv j hj]
    unfold quarterValues
    rw [candidates_word _ _ _ he (hc.mask e he),Offset.add_add]
  have hbound (j : Nat) (hj : j<4) (e : Nat) (he : e<4) :
      (vword (a.v wideRegs[j]!) e).toNat<2^23 := by
    rw [hval j hj e he]; exact candidate_bound _ _
  have hbranch : a.gpr .x6=0 ↔ ∀j<4,∀e<4,(vword (a.v wideRegs[j]!) e).toNat<q := by
    rw [hflag,wideMask_all hc]
    constructor
    · intro h j hj e he; rw [hval j hj e he]; exact h e he j hj
    · intro h e he j hj; rw [←hval j hj e he]; exact h j hj e he
  have hresult : laneFold a.v wideLanes L=candidateFold s.mem (s.gpr .x2) 16 L := by
    rw [laneFold_map,wideLanes,List.map_map,candidateFold]
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj16 := List.mem_range.mp hj
    dsimp only [Function.comp_apply]
    rw [hval (j/4) (by omega) (j%4) (by omega)]
    rw [show 12*(j/4)+3*(j%4)=3*j by omega]
  refine WP.mono (wideChoice_ok (p := p) (L := L) hbound hbranch
    (by rw [ha.only.get .x9]; exact hc.qreg)
    (by rw [ha.only.get .x3]; exact h3) (by rw [ha.only.get .x4]; exact h4) hL
    (by rw [ha.only.mem]; exact hst)
    (fun i hi => by rw [ha.only.wr]; exact hw i hi)
    (fun j hj => by rw [ha.only.wr,ha.only.get .x3]; exact hw16 j hj))
    fun t ⟨ht,hvec,hframe,hp,hcount,hstored⟩ => ?_
  rw [hresult] at hp hcount hstored
  refine ⟨ha.only.keep.trans ht,by rw [←ha.only.mem]; exact hframe,?_,hp,hcount,hstored⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hvec,ha.vectors .v3 (by decide)]; exact hc.index
  · intro e he; rw [hvec,ha.vectors .v4 (by decide)]; exact hc.mask e he
  · intro e he; rw [hvec,ha.vectors .v5 (by decide)]; exact hc.modulus e he
  · rw [ht.get .x12,ha.only.get .x12]; exact hc.ones
  · rw [ht.get .x9,ha.only.get .x9]; exact hc.qreg

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
