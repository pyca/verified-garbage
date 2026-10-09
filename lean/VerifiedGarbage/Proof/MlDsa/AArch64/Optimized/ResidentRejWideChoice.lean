import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideStore

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def wideLanes : List (VReg×Nat) :=
 (List.range 16).map fun j => (wideRegs[j/4]!,j%4)

theorem wideLanes_mem {r : VReg} {e : Nat} (h : (r,e)∈wideLanes) :
    ∃j<4,r=wideRegs[j]! ∧ e<4 := by
  obtain ⟨k,hk,he⟩ := List.mem_map.mp h
  have hk16 := List.mem_range.mp hk
  cases he
  exact ⟨k/4,by omega,rfl,by omega⟩

theorem wideLanes_all {v : VReg → BitVec 128} {L : List Zq}
    (h : ∀j<4,∀e<4,(vword (v wideRegs[j]!) e).toNat<q) :
    laneFold v wideLanes L=widePrefix v L 4 := by
  rw [laneFold_all _ _ (by
    intro r e hr
    obtain ⟨j,hj,rfl,he⟩ := wideLanes_mem hr
    exact h j hj e he)]
  have hh : wideLanes.map (fun (r,e) => Fin.ofNat q (vword (v r) e).toNat)=
      fourValues (v .v16)++fourValues (v .v17)++fourValues (v .v18)++fourValues (v .v19) := rfl
  rw [hh]
  simp only [widePrefix,List.append_assoc]
  rfl

/-- All sixteen fast stores and the rejection fallback preserve the same
ordered accepted sequence. -/
theorem wideChoice_ok {s : State} {p : Addr} {L : List Zq}
    (hz : ∀j<4,∀e<4,(vword (s.v wideRegs[j]!) e).toNat<2^23)
    (hf : s.gpr .x6=0 ↔ ∀j<4,∀e<4,(vword (s.v wideRegs[j]!) e).toNat<q)
    (h9 : (s.gpr .x9).toNat=q) (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length+16≤256)
    (hst : Stored s.mem p L)
    (hw : ∀i<256,InRegions s.wr (coeffAddr p i) 4)
    (hw16 : ∀j<4,InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.ite (.zero .x .x6) (.block wideAccept) (.block wideReject)) s fun t =>
      Keep fallbackRegs s t ∧ t.v=s.v ∧ Frame [polyR p] s.mem t.mem ∧
      t.gpr .x3=coeffAddr p (laneFold s.v wideLanes L).length ∧
      (t.gpr .x4).toNat=256-(laneFold s.v wideLanes L).length ∧
      Stored t.mem p (laneFold s.v wideLanes L) := by
  by_cases he : s.gpr .x6=0
  · have ha := hf.mp he
    refine WP.ite true (by rw [eval_zero,he]; rfl) (fun _ => ?_) (fun h => Bool.noConfusion h)
    rw [wideLanes_all ha]
    refine WP.mono (wideAccept_ok hst hL h3 h4 ha hw16) fun t ⟨hk,hv,hf,hp,hc,hs⟩ =>
      ⟨hk.mono (by decide),hv,hf,hp,hc,hs⟩
  · refine WP.ite false (by rw [eval_zero,show (s.gpr .x6 == 0)=false from beq_eq_false_iff_ne.mpr he])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    have hcode : wideReject=lanesCode wideLanes := rfl
    rw [hcode]
    exact lanes_ok wideLanes (by
      intro r e hr
      obtain ⟨j,hj,rfl,he'⟩ := wideLanes_mem hr
      exact ⟨he',hz j hj e he'⟩) h9 h3 h4 hL hst hw

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
