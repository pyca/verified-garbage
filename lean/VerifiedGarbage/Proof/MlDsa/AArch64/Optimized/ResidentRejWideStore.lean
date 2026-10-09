import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejChoice

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
  | succ n ih => simp only [widePrefix,List.length_append,fourValues,List.length_cons,List.length_nil,ih]; omega

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
    refine WP.mono (ih (by omega) (by omega) (fun j hj => hv j (by omega))
      (fun j hj => hw j (by omega))) fun a ⟨ha,hav,haf,has⟩ => ?_
    have hp : a.gpr .x3+BitVec.ofNat 64 (16*n)=coeffAddr p (widePrefix s.v L n).length := by
      rw [ha.get .x3,h3,widePrefix_length,coeffAddr,coeffAddr,Offset.add_add]
      congr 2 <;> omega
    refine wp_strq (a := coeffAddr p (widePrefix s.v L n).length)
      (by constructor <;> omega) hp (by rw [←hp,ha.wr,ha.get .x3]; exact hw n (by omega))
      fun t ht => wp_nil ?_
    refine ⟨(ha.trans ht.keep).mono (by simp),?_,?_,?_⟩
    · rw [ht.v,hav]
    · rw [ht.mem]
      exact haf.write (List.mem_singleton_self _) _ (Offset.contains_base p
        (by rw [widePrefix_length]; omega) (by rw [widePrefix_length]; omega))
    · rw [ht.mem,widePrefix,hav]
      apply stored_append_four has (by rw [widePrefix_length]; omega) rfl
      intro e he
      have hh := hv n (by omega) e he
      rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl
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
      omega
    · rw [ht.mem,hb.mem]; exact has
  · intro t ⟨⟨hk,hf,hp,hc,hs⟩,hv'⟩
    exact ⟨hk,hv'.trans hav,hf,hp,hc,hs⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
