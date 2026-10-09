import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFallback

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
