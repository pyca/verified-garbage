module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejChoice
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFourStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejWideValue

/-! ### `MlDsa.AArch64.Optimized.ResidentRejWideChoice`, which only this module used -/

section

/-! ## From `ResidentRejWideStore.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

def widePrefix (v : VReg → BitVec 128) (L : List Zq) : Nat → List Zq
 | 0 => L
 | n+1 => widePrefix v L n ++ fourValues (v wideRegs[n]!)

theorem widePrefix_length (v : VReg → BitVec 128) (L : List Zq) (n : Nat) :
    (widePrefix v L n).length=L.length+4*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [widePrefix,List.length_append,fourValues,List.length_cons,List.length_nil,ih]; omega_using []

/-- The four vector writes preserve the accepted prefix and append precisely
sixteen candidates, without changing pointers until all stores are complete. -/
theorem wideStores_ok (n : Nat) (hn : n≤4) {s : State} {p : Addr} {L : List Zq}
    (hst : Stored s.mem p L) (hsize : L.length+4*n≤256)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (hv : ∀j<n,∀e<4,(vword (s.v wideRegs[j]!) e).toNat<q)
    (hw : ∀j<n,InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block ((List.range n).map (fun j => .strq wideRegs[j]! .x3 (16*j)))) s fun t =>
      Keep [] s t ∧ t.v=s.v ∧ Frame [polyR p] s.mem t.mem ∧
      Stored t.mem p (widePrefix s.v L n) := by
  induction n with
  | zero => exact WP.block_nil_iff.mpr ⟨Keep.refl _ _,rfl,Frame.refl _ _,hst⟩
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.map_cons,List.map_nil,WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) (by omega_using [hsize]) (fun j hj => hv j (by omega_using [hj]))
      (fun j hj => hw j (by omega_using [hj]))) fun a ⟨ha,hav,haf,has⟩ => ?_
    have hp : a.gpr .x3+BitVec.ofNat 64 (16*n)=coeffAddr p (widePrefix s.v L n).length := by
      rw [ha.get .x3,h3,widePrefix_length,coeffAddr,coeffAddr,Offset.add_add]
      congr 2 <;> omega_using []
    refine wp_strq (a := coeffAddr p (widePrefix s.v L n).length)
      (by constructor <;> omega_arith) hp (by rw [←hp,ha.wr,ha.get .x3]; exact hw n (by omega_using []))
      fun t ht => wp_nil ?_
    refine ⟨(ha.trans ht.keep).mono (by simp),?_,?_,?_⟩
    · rw [ht.v,hav]
    · rw [ht.mem]
      exact haf.write (List.mem_singleton_self _) _ (Offset.contains_base p
        (by rw [widePrefix_length]; omega_using [hsize]) (by rw [widePrefix_length]; omega_using [hsize]))
    · rw [ht.mem,widePrefix,hav]
      apply stored_append_four has (by rw [widePrefix_length]; omega_using [hsize]) rfl
      intro e he
      have hh := hv n (by omega_using []) e he
      rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega_using [he]) with rfl | rfl | rfl | rfl
      all_goals exact (Nat.mod_eq_of_lt hh).symm

/-- Pointer updates following the four stores agree with sixteen accepted
scalar candidates. -/
theorem wideAccept_ok {s : State} {p : Addr} {L : List Zq}
    (hst : Stored s.mem p L) (hsize : L.length+16≤256)
    (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length)
    (hv : ∀j<4,∀e<4,(vword (s.v wideRegs[j]!) e).toNat<q)
    (hw : ∀j<4,InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block wideAccept) s fun t =>
      Keep [.x3,.x4] s t ∧ t.v=s.v ∧ Frame [polyR p] s.mem t.mem ∧
      t.gpr .x3=coeffAddr p (widePrefix s.v L 4).length ∧
      (t.gpr .x4).toNat=256-(widePrefix s.v L 4).length ∧
      Stored t.mem p (widePrefix s.v L 4) := by
  rw [wideAccept,WP.block_append_iff]
  refine WP.mono (wideStores_ok 4 (by decide) hst hsize h3 hv hw)
    fun a ⟨ha,hav,haf,has⟩ => ?_
  refine WP.mono (WP.keepV (Q := fun t =>
    Keep [.x3,.x4] s t ∧ Frame [polyR p] s.mem t.mem ∧
    t.gpr .x3=coeffAddr p (widePrefix s.v L 4).length ∧
    (t.gpr .x4).toNat=256-(widePrefix s.v L 4).length ∧
    Stored t.mem p (widePrefix s.v L 4))
    (by decide) (wp_addImm (by decide) fun b hb eb =>
    wp_subImm (by decide) fun t ht et => wp_nil ?_)) ?_
  · refine ⟨((ha.trans hb.keep).trans ht.keep).mono (by simp),?_,?_,?_,?_⟩
    · rw [ht.mem,hb.mem]; exact haf
    · rw [ht.get .x3,eb,ha.get .x3,h3,widePrefix_length,coeffAddr,coeffAddr,Offset.add_add]
      congr 1
    · rw [et,hb.get .x4,ha.get .x4,BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat]
      rw [h4,widePrefix_length]
      omega_using [hsize]
    · rw [ht.mem,hb.mem]; exact has
  · intro t ⟨⟨hk,hf,hp,hc,hs⟩,hv'⟩
    exact ⟨hk,hv'.trans hav,hf,hp,hc,hs⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejWideChoice.lean` -/

section

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
  exact ⟨k/4,by omega_using [hk16],rfl,by omega_using []⟩

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

end

end

end


@[expose] public section

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
    rw [hval (j/4) (by omega_using [hj16]) (j%4) (by omega_using [])]
    rw [show 12*(j/4)+3*(j%4)=3*j by omega_using []]
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
