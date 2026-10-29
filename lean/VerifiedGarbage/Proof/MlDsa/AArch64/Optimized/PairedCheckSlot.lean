module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinalMemory

import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/PairedCheckOutput.lean`, which only this module imported.
section

/-! ## From `PairedCheckRead.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- A check sequence preserves any untouched vector, independently of flags. -/
theorem checkRun_read_other (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) (a : Addr)
    (hs : ∀i∈js,Mem.Sep a 16 (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16) :
    (checkRun hint v out aux c d js).mem.read a 16=d.mem.read a 16 := by
  induction js generalizing d with
  | nil => rfl
  | cons i js ih =>
    change (checkRun hint v out aux c (checkStep hint ((v i.1)[i.2.val])
      (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val))
      (aux+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) c d) js).mem.read a 16=_
    rw [ih _ (fun j hj => hs j (List.mem_cons_of_mem _ hj))]
    exact Mem.read_write_sep (hs i (by simp)) (by decide)

/-- The z path preserves the hint count accumulator exactly. -/
theorem checkRun_z_count (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) :
    (checkRun false v out aux c d js).count=d.count := by
  induction js generalizing d with
  | nil => rfl
  | cons i js ih =>
    simp only [checkRun]
    exact ih _

theorem finalPass_z_count (work out aux : Addr) (c : CheckConstants) (d : CheckData) (u : Nat) :
    (finalPassData false work out aux c d u).count=d.count := by
  induction u with
  | zero => rfl
  | succ u ih => rw [finalPassData,checkRun_z_count,ih]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedCheckOutput.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (laneVector reduceWord hintWord)

def checkOutput (hint : Bool) (raw low high : BitVec 128) (c : CheckConstants) : BitVec 128 :=
  laneVector fun e => if hint then
    hintWord (vword c.gamma e) (reduceWord (vword raw e)+vword low e) (vword high e)
    else reduceWord (vword raw e+vword low e)

theorem checkStep_read_self (hint : Bool) (raw : BitVec 128) (out aux : Addr)
    (c : CheckConstants) (d : CheckData) :
    (checkStep hint raw out aux c d).mem.read out 16=
      checkOutput hint raw (d.mem.read out 16) (d.mem.read aux 16) c := by
  have hm : (checkStep hint raw out aux c d).mem =
      d.mem.write out 16 (checkOutput hint raw (d.mem.read out 16) (d.mem.read aux 16) c) := by
    cases hint <;> simp only [checkStep,checkOutput,Bool.false_eq_true,ite_false,ite_true]
  rw [hm]
  exact Mem.readW_writeW_self d.mem out 16
    (checkOutput hint raw (d.mem.read out 16) (d.mem.read aux 16) c) (by decide)

/-- Once a vector is checked, the remaining distinct checks preserve its output. -/
theorem checkRun_head_output (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (i : Fin 2 × Fin 8) (js : List (Fin 2 × Fin 8))
    (hs : ∀j∈js,Mem.Sep (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16
      (out+BitVec.ofNat 64 (1024*j.1.val+128*j.2.val)) 16) :
    (checkRun hint v out aux c d (i::js)).mem.read (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16=
      checkOutput hint ((v i.1)[i.2.val])
        (d.mem.read (out+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16)
        (d.mem.read (aux+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)) 16) c := by
  rw [checkRun,checkRun_read_other _ _ _ _ _ _ _ _ hs,checkStep_read_self]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

def checkAddr (base : Addr) (i : Fin 2 × Fin 8) : Addr :=
  base+BitVec.ofNat 64 (1024*i.1.val+128*i.2.val)

theorem checkAddr_sep (base : Addr) {i j : Fin 2 × Fin 8} (hne : j≠i) :
    Mem.Sep (checkAddr base i) 16 (checkAddr base j) 16 := by
  have hd : j.1.val≠i.1.val ∨ j.2.val≠i.2.val := by
    by_contra h
    simp only [not_or,not_not] at h
    exact hne (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  exact Offset.sep base (by omega) (by omega) (by omega)

/-- Every checked vector has exactly its prescribed output, using its original
inputs; arbitrary earlier and later disjoint stores cannot alter the result. -/
theorem checkRun_read_slot (hint : Bool) (v : Values) (out aux : Addr) (c : CheckConstants)
    (d : CheckData) (js : List (Fin 2 × Fin 8)) (i : Fin 2 × Fin 8)
    (hi : i∈js) (hn : js.Nodup)
    (hs : ∀j∈js,j≠i → Mem.Sep (checkAddr out i) 16 (checkAddr out j) 16)
    (ha : ∀j∈js,Mem.Sep (checkAddr aux i) 16 (checkAddr out j) 16) :
    (checkRun hint v out aux c d js).mem.read (checkAddr out i) 16=
      checkOutput hint ((v i.1)[i.2.val]) (d.mem.read (checkAddr out i) 16)
        (d.mem.read (checkAddr aux i) 16) c := by
  induction js generalizing d with
  | nil => simp at hi
  | cons j js ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : j=i
    · subst j
      exact checkRun_head_output hint v out aux c d i js
        (fun j hj => hs j (List.mem_cons_of_mem _ hj) (by intro he; subst j; exact hn'.1 hj))
    · have hit : i∈js := (List.mem_cons.mp hi).resolve_left (Ne.symm he)
      simp only [checkRun]
      rw [ih _ hit hn'.2 (fun k hk => hs k (List.mem_cons_of_mem _ hk))
        (fun k hk => ha k (List.mem_cons_of_mem _ hk))]
      have ho : (checkStep hint ((v j.1)[j.2.val]) (checkAddr out j) (checkAddr aux j) c d).mem.read
          (checkAddr out i) 16=d.mem.read (checkAddr out i) 16 :=
        Mem.read_write_sep (hs j (by simp) he) (by decide)
      have haux : (checkStep hint ((v j.1)[j.2.val]) (checkAddr out j) (checkAddr aux j) c d).mem.read
          (checkAddr aux i) 16=d.mem.read (checkAddr aux i) 16 :=
        Mem.read_write_sep (ha j (by simp)) (by decide)
      simp only [checkAddr] at ho haux ⊢
      rw [ho,haux]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
