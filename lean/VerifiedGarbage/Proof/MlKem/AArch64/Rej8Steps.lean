module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Prefix

import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
import Mathlib.Tactic.SplitIfs

/-! # Stable vector rejection agrees with successive scalar sampling steps -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64.Rej8

def acceptValue (L : List Zq) (v : Nat) : List Zq :=
  if v<q then L++[ofNat v] else L

theorem acceptValue_length (L : List Zq) (v : Nat) :
    (acceptValue L v).length≤L.length+1 := by
  unfold acceptValue
  split <;> simp_all

theorem fold_accept (L : List Zq) (is : List Nat) (f : Nat → Nat) :
    is.foldl (fun a i => acceptValue a (f i)) L =
      L++((is.filter fun i => decide (f i<q)).map fun i => ofNat (f i)) := by
  induction is generalizing L with
  | nil => simp
  | cons i is ih =>
    simp only [List.foldl_cons,ih,List.filter_cons]
    unfold acceptValue
    by_cases h : f i<q <;> simp [h,List.append_assoc]

theorem acceptedValues_filter (s : State) :
    acceptedValues s =
      ((List.range 8).filter fun i => decide ((candidate s.mem (s.gpr .x2) i).toNat<q)).map
        fun i => ofNat (candidate s.mem (s.gpr .x2) i).toNat := by
  unfold acceptedValues acceptedLanes
  have hf : (List.range 8).filter (fun i => (maskAt s / 2^i)%2 == 1) =
      (List.range 8).filter (fun i => decide ((candidate s.mem (s.gpr .x2) i).toNat<q)) := by
    apply List.filter_congr
    intro i hi
    have hb : i<8 := List.mem_range.mp hi
    rw [maskAt,acceptanceMask_bits _ hb]
    rw [candidatesAt,parsed_candidate _ _ hb]
  rw [hf]
  apply List.map_congr_left
  intro i hi
  have hb : i<8 := List.mem_range.mp (List.mem_filter.mp hi).1
  rw [candidatesAt,parsed_candidate _ _ hb]

theorem sampleStepCap_accept {L : List Zq} (h : L.length+2≤256) (a b c : Byte) :
    sampleStepCap L a b c =
      acceptValue (acceptValue L (a.toNat+256*(b.toNat%16))) (b.toNat/16+16*c.toNat) := by
  have hn : n=256 := rfl
  have hl : L.length≠n := by omega
  have hlen := acceptValue_length L (a.toNat+256*(b.toNat%16))
  have hroom : (acceptValue L (a.toNat+256*(b.toNat%16))).length<n := by omega
  simp only [sampleStepCap,ite_eq_right hl,sampleStep,acceptValue] at *
  simp only [hroom,and_true]


theorem four_steps (L : List Zq) (B : Nat → Byte) (h : L.length+8≤256) :
    sampleAfter L B 4 =
      [(B 0).toNat+256*((B 1).toNat%16), (B 1).toNat/16+16*(B 2).toNat,
       (B 3).toNat+256*((B 4).toNat%16), (B 4).toNat/16+16*(B 5).toNat,
       (B 6).toNat+256*((B 7).toNat%16), (B 7).toNat/16+16*(B 8).toNat,
       (B 9).toNat+256*((B 10).toNat%16), (B 10).toNat/16+16*(B 11).toNat].foldl
        acceptValue L := by
  let a₁ := acceptValue L ((B 0).toNat+256*((B 1).toNat%16))
  let a₂ := acceptValue a₁ ((B 1).toNat/16+16*(B 2).toNat)
  let a₃ := acceptValue a₂ ((B 3).toNat+256*((B 4).toNat%16))
  let a₄ := acceptValue a₃ ((B 4).toNat/16+16*(B 5).toNat)
  let a₅ := acceptValue a₄ ((B 6).toNat+256*((B 7).toNat%16))
  let a₆ := acceptValue a₅ ((B 7).toNat/16+16*(B 8).toNat)
  have h₁ : a₁.length≤L.length+1 := acceptValue_length _ _
  have h₂ : a₂.length≤a₁.length+1 := acceptValue_length _ _
  have h₃ : a₃.length≤a₂.length+1 := acceptValue_length _ _
  have h₄ : a₄.length≤a₃.length+1 := acceptValue_length _ _
  have h₅ : a₅.length≤a₄.length+1 := acceptValue_length _ _
  have h₆ : a₆.length≤a₅.length+1 := acceptValue_length _ _
  simp only [sampleAfter]
  rw [sampleStepCap_accept (by omega : L.length+2≤256)]
  change sampleStepCap (sampleStepCap (sampleStepCap a₂ _ _ _) _ _ _) _ _ _ = _
  rw [sampleStepCap_accept (by omega : a₂.length+2≤256)]
  change sampleStepCap (sampleStepCap a₄ _ _ _) _ _ _ = _
  rw [sampleStepCap_accept (by omega : a₄.length+2≤256)]
  change sampleStepCap a₆ _ _ _ = _
  rw [sampleStepCap_accept (by omega : a₆.length+2≤256)]
  rfl


theorem batch_steps (s : State) (L : List Zq) (h : L.length+8≤256) :
    L++acceptedValues s = sampleAfter L (fun i => s.mem (s.gpr .x2+BitVec.ofNat 64 i)) 4 := by
  rw [acceptedValues_filter,←fold_accept]
  rw [four_steps L _ h]
  change [0,1,2,3,4,5,6,7].foldl
    (fun a i => acceptValue a (candidate s.mem (s.gpr .x2) i).toNat) L = _
  simp only [List.foldl_cons,List.foldl_nil]
  rw [candidate_even _ _ 0,candidate_odd _ _ 0,
    candidate_even _ _ 1,candidate_odd _ _ 1,
    candidate_even _ _ 2,candidate_odd _ _ 2,
    candidate_even _ _ 3,candidate_odd _ _ 3]
  simp only [BitVec.add_assoc]
  rfl

end VG.Proof.MlKem.AArch64.Rej8
