import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseLocalTable

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def finalValue (i : Nat) : Nat :=
  if i<4 then VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (7-i)
  else if i<6 then VG.Impl.MlDsa.AArch64.Optimized.Inverse.z (3-(i-4))
  else (VG.Impl.MlDsa.AArch64.Optimized.Inverse.z 1*16382)%8380417

def finalZ (i : Nat) (_e : Nat) : Int := finalValue i

def finalRootReg (i : Nat) : VReg := if i<4 then .v22 else if i<6 then .v23 else .v30
def finalRecipReg (i : Nat) : VReg := if i<4 then .v28 else if i<6 then .v29 else .v30
def finalRootLane (i : Nat) : Nat := if i<4 then i else if i<6 then i-4 else 2
def finalRecipLane (i : Nat) : Nat := if i<4 then i else if i<6 then i-4 else 3

def finalLoad (i : Nat) : List Instr :=
  [.vop (.dupE .s4 .v20 (finalRootReg i) (finalRootLane i)),
   .vop (.dupE .s4 .v21 (finalRecipReg i) (finalRecipLane i))]

structure FinalRoots (s : State) : Prop where
  root : ∀ i : Fin 7, vword (s.v (finalRootReg i.val)) (finalRootLane i.val)=BitVec.ofInt 32 (finalZ i.val 0)
  recip : ∀ i : Fin 7, vword (s.v (finalRecipReg i.val)) (finalRecipLane i.val)=BitVec.ofInt 32 (reciprocal (finalZ i.val 0))
  q : ∀ e<4, vword (s.v .v31) e=8380417#32

def finalConstants : List VReg := [.v22,.v23,.v28,.v29,.v30,.v31]

theorem FinalRoots.frame {s t : State} {vs : List VReg} (h : FinalRoots s)
    (hc : VChg vs s t) (hv : ∀ r∈finalConstants, r∉vs) : FinalRoots t := by
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [hc.get _ (hv _ ((show ∀ i : Fin 7, finalRootReg i.val∈finalConstants by decide +kernel) i))]
    exact h.root i
  · intro i
    rw [hc.get _ (hv _ ((show ∀ i : Fin 7, finalRecipReg i.val∈finalConstants by decide +kernel) i))]
    exact h.recip i
  · intro e he
    rw [hc.get _ (hv _ (by decide))]
    exact h.q e he

theorem finalZ_range (i e : Nat) : 0≤finalZ i e ∧ finalZ i e<8380417 := by
  have hz (j : Nat) : VG.Impl.MlDsa.AArch64.Optimized.Inverse.z j<8380417 := Nat.mod_lt _ (by decide)
  have hv : finalValue i<8380417 := by
    unfold finalValue
    split_ifs
    · exact hz _
    · exact hz _
    · exact Nat.mod_lt _ (by decide)
  exact ⟨Int.natCast_nonneg _,Int.ofNat_lt.mpr hv⟩

theorem finalLoad_ok (i : Fin 7) {s : State} {rest : List Instr} {Q : State → Prop}
    (h : FinalRoots s)
    (k : ∀ t, VChg [.v20,.v21] s t → FinalRoots t →
      (∀ e<4, vword (t.v .v20) e=BitVec.ofInt 32 (finalZ i.val e)) →
      (∀ e<4, vword (t.v .v21) e=BitVec.ofInt 32 (reciprocal (finalZ i.val e))) →
      WP isa (.block rest) t Q) :
    WP isa (.block (finalLoad i.val ++ rest)) s Q := by
  have hi : finalRootLane i.val<4 ∧ finalRecipLane i.val<4 ∧ finalRecipReg i.val≠.v20 :=
    (show ∀ i : Fin 7, finalRootLane i.val<4 ∧ finalRecipLane i.val<4 ∧ finalRecipReg i.val≠.v20 by decide +kernel) i
  unfold finalLoad
  simp only [List.cons_append,List.nil_append]
  have he (t : State) (d a : VReg) (j : Nat) (hj : j<4) :
      (VOp.dupE .s4 d a j).eval t=some (d,
        VArr.s4.map2 (fun w _ _ => (t.v a).extractLsb' (w*j) w) 0 0) := by
    simp only [VOp.eval,VArr.esize,show 128/32=4 by decide,hj,ite_true]
  refine VG.Proof.MlKem.AArch64.wp_vop (he s .v20 _ _ hi.1) fun s₁ h₁ =>
    VG.Proof.MlKem.AArch64.wp_vop (he s₁ .v21 _ _ hi.2.1) fun t h₂ => ?_
  have hc' : VChg [.v20,.v21] s t := h₁.chg.trans h₂.chg
  refine k t hc' (h.frame hc' (by decide)) ?_ ?_
  · intro e he
    rw [h₂.get .v20,h₁.v,VG.AArch64.vword_map2 _ _ _ he]
    exact h.root i
  · intro e he
    rw [h₂.v,VG.AArch64.vword_map2 _ _ _ he,h₁.get _ hi.2.2]
    exact h.recip i

def finalPlan : RootPlan where
  load := finalLoad
  value := finalZ
  invariant := FinalRoots
  range i e _ := finalZ_range i.val e
  stable i _ _ hc hs := hs.frame hc ((show ∀ i : Fin 7, ∀ r∈finalConstants, r∉stageClobs i.val by decide +kernel) i)
  load_ok i _ _ _ hs k := finalLoad_ok i hs fun t hc ht hz hb => k t hc ht hz hb ht.q

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
