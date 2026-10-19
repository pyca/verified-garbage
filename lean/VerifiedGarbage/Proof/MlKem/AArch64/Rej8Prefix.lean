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

/-- Stores beyond the compacted prefix are irrelevant: later batches may
overwrite them, and bounded failure clears the entire remaining suffix. -/
theorem append_cvW {w16 : Bool} {L R : List Zq} {i : Nat} (hi : L.length≤i) :
    Sample.cvW w16 (L++R) i=Sample.cvW w16 R (i-L.length) := by
  simp only [Sample.cvW,List.getD_eq_getElem?_getD,List.getElem?_append_right hi]

theorem append_cvW_left {w16 : Bool} {L R : List Zq} {i : Nat} (hi : i<L.length) :
    Sample.cvW w16 (L++R) i=Sample.cvW w16 L i := by
  simp only [Sample.cvW,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

/-- `batch_prefix` with either width. -/
theorem batch_prefixW (w16 : Bool) (s : State) {p : Addr} {L : List Zq}
    (h3 : s.gpr .x3=cAddr w16 p L.length) (hroom : L.length+8≤256)
    (hz : ∀i<8,vhalf (s.v .v21) i=0) (hp : Scalar.CoeffsW w16 s.mem p L) :
    Scalar.CoeffsW w16 (updatedMem s w16) p (L++acceptedValues s) := by
  intro i hi
  have hn : acceptedCount s≤8 := accepted_length (maskAt s)
  have hlen : i<L.length+acceptedCount s := by
    simpa only [List.length_append,acceptedValues_length] using hi
  have hi256 : i<256 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [coeffAtW_updatedMem w16 s h3 hroom hi256 hz]
  by_cases hbefore : i<L.length
  · rw [ite_eq_right (by omega),hp i hbefore,append_cvW_left hbefore]
  · have hk : i-L.length<acceptedCount s := by omega
    rw [ite_eq_left ⟨by omega,by omega⟩,ite_eq_left hk,append_cvW (by omega)]
    have hv := accepted_value_lt s hk
    have he : (acceptedValues s).getD (i-L.length) 0 =
        ofNat (vhalf (candidatesAt s) ((acceptedLanes (maskAt s)).getD (i-L.length) 0)).toNat := by
      simp only [acceptedValues,List.getD_eq_getElem?_getD,List.getElem?_map,
        List.getElem?_eq_getElem (show i-L.length<(acceptedLanes (maskAt s)).length from hk),
        Option.map_some,Option.getD_some]
    have hq : q = 3329 := rfl
    simp only [Sample.cvW,he,BitVec.toNat_ofNat,val_ofNat]
    cases w16 <;> simp only [cw,Bool.false_eq_true,ite_false,ite_true,Nat.reducePow,hq] <;> omega

end VG.Proof.MlKem.AArch64.Rej8
