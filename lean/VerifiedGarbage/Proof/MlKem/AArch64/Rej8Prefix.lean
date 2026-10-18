module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory

/-! # The batch appends exactly the accepted coefficients to the existing prefix -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Rej8
open VG.Proof.MlKem.AArch64.Sample (cv)

def acceptedValues (s : State) : List Zq :=
  (acceptedLanes (maskAt s)).map fun i => ofNat (vhalf (candidatesAt s) i).toNat

theorem acceptedValues_length (s : State) : (acceptedValues s).length=acceptedCount s := by
  simp only [acceptedValues,acceptedCount,List.length_map]

theorem accepted_value_lt (s : State) {k : Nat} (hk : k<acceptedCount s) :
    (vhalf (candidatesAt s) ((acceptedLanes (maskAt s)).getD k 0)).toNat < 3329 := by
  have hm : (acceptedLanes (maskAt s)).getD k 0 ∈ acceptedLanes (maskAt s) := by
    have h := List.getElem_mem (l := acceptedLanes (maskAt s)) hk
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some] using h
  have hi := accepted_mem hm
  have hb := (List.mem_filter.mp hm).2
  change ((acceptanceMask (candidatesAt s) / 2^((acceptedLanes (maskAt s)).getD k 0))%2 == 1) = true at hb
  rw [acceptanceMask_bits _ hi] at hb
  exact of_decide_eq_true hb

theorem cv_map (is : List Nat) (f : Nat → Nat) {k : Nat} (hk : k<is.length)
    (hb : f (is.getD k 0)<q) :
    cv (is.map fun i => ofNat (f i)) k=BitVec.ofNat 32 (f (is.getD k 0)) := by
  have he : (is.map fun i => ofNat (f i)).getD k 0=ofNat (f (is.getD k 0)) := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_eq_getElem hk,Option.map_some,Option.getD_some]
  rw [cv,Sample.cvW,he,val_ofNat,Nat.mod_eq_of_lt hb]; rfl

theorem accepted_cv (s : State) {k : Nat} (hk : k<acceptedCount s) :
    cv (acceptedValues s) k =
      BitVec.ofNat 32 (vhalf (candidatesAt s) ((acceptedLanes (maskAt s)).getD k 0)).toNat :=
  cv_map (acceptedLanes (maskAt s)) (fun i => (vhalf (candidatesAt s) i).toNat)
    hk (accepted_value_lt s hk)

theorem append_cv {L R : List Zq} {i : Nat} (hi : L.length≤i) :
    cv (L++R) i=cv R (i-L.length) := by
  simp only [cv,Sample.cvW,List.getD_eq_getElem?_getD,List.getElem?_append_right hi]

theorem append_cv_left {L R : List Zq} {i : Nat} (hi : i<L.length) :
    cv (L++R) i=cv L i := by
  simp only [cv,Sample.cvW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

/-- Stores beyond the compacted prefix are irrelevant: later batches may
overwrite them, and bounded failure clears the entire remaining suffix. -/
theorem batch_prefix (s : State) {p : Addr} {L : List Zq}
    (h3 : s.gpr .x3=coeffAddr p L.length) (hroom : L.length+8≤256)
    (hz : ∀i<8,vhalf (s.v .v21) i=0) (hp : Scalar.Coeffs s.mem p L) :
    Scalar.Coeffs (updatedMem s) p (L++acceptedValues s) := by
  intro i hi
  have hn : acceptedCount s≤8 := accepted_length (maskAt s)
  have hlen : i<L.length+acceptedCount s := by
    simpa only [List.length_append,acceptedValues_length] using hi
  have hi256 : i<256 := by omega
  rw [coeffAt_updatedMem s h3 hroom hi256]
  by_cases hbefore : i<L.length
  · rw [ite_eq_right (by omega),ite_eq_right (by omega),hp i hbefore,
      append_cv_left hbefore]
  · have hk : i-L.length<acceptedCount s := by omega
    rw [append_cv (by omega),accepted_cv s hk]
    have hm : maskAt s<256 := acceptanceMask_bound (candidatesAt s)
    by_cases hlo : i<L.length+4
    · rw [ite_eq_left ⟨by omega,hlo⟩]
      apply BitVec.eq_of_toNat_eq
      have hv := (widened_coeffs (candidatesAt s) (s.v .v21) hm hz (i := i-L.length) (by omega)).1
      rw [ite_eq_left (show i-L.length < (acceptedLanes (maskAt s)).length from hk)] at hv
      rw [hv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      exact Nat.lt_trans (accepted_value_lt s hk) (by decide)
    · rw [ite_eq_right (by omega),ite_eq_left ⟨by omega,by omega⟩]
      apply BitVec.eq_of_toNat_eq
      have hv := (widened_coeffs (candidatesAt s) (s.v .v21) hm hz (i := i-(L.length+4)) (by omega)).2
      rw [show 4+(i-(L.length+4))=i-L.length by omega,ite_eq_left (show i-L.length < (acceptedLanes (maskAt s)).length from hk)] at hv
      rw [hv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      exact Nat.lt_trans (accepted_value_lt s hk) (by decide)

end VG.Proof.MlKem.AArch64.Rej8
