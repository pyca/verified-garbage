import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPackedBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedShape

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (vr)

def bankRegs (p : Fin 2) : Vector VReg 8 := Vector.ofFn fun j => vr (8*p.val+j.val)
abbrev Values := Fin 2 → Vector (BitVec 128) 8
def Banks (s : State) (v : Values) : Prop := ∀p,Bank s (bankRegs p) (v p)

theorem bankRegs_inj (p : Fin 2) : Function.Injective (fun j : Fin 8 => (bankRegs p)[j.val]) := by
  intro i j h
  simp only [bankRegs,Vector.getElem_ofFn] at h
  apply Fin.ext
  have he := bank_injective (by omega) (by omega) h
  omega

theorem bankRegs_safe (p : Fin 2) (j : Fin 8) :
    (bankRegs p)[j.val]∉[.v24,.v25,.v26,.v27] := by
  have h := bank_safe (j := 8*p.val+j.val) (by omega)
  simp only [bankRegs,Vector.getElem_ofFn,List.mem_cons,List.not_mem_nil,or_false] at *
  grind only

theorem bankRegs_cross (p q : Fin 2) (hpq : p≠q) (i j : Fin 8) :
    (bankRegs p)[i.val]≠(bankRegs q)[j.val] := by
  intro h
  simp only [bankRegs,Vector.getElem_ofFn] at h
  have he := bank_injective (by omega) (by omega) h
  apply hpq
  apply Fin.ext
  omega

/-- Updating one bank preserves the entire other polynomial bank. -/
theorem Banks.packed {s t : State} {v : Values} (hs : Banks s v)
    (p : Fin 2) (i j : Fin 8) (len : Nat) (z : Nat → Int)
    (hc : VChg (packedClobs (bankRegs p) i j) s t)
    (hv : Bank t (bankRegs p) (Inverse.packedValues (v p) i j len z)) :
    Banks t (fun q => if q=p then Inverse.packedValues (v p) i j len z else v q) := by
  intro q
  by_cases hp : q=p
  · subst q
    simpa only [ite_true] using hv
  · simp only [hp,ite_false]
    intro k
    rw [hc.get _ ?_,hs q k]
    have ht := bankRegs_safe q k
    have hi := bankRegs_cross q p hp k i
    have hj := bankRegs_cross q p hp k j
    simp only [packedClobs,List.mem_cons,List.not_mem_nil,or_false] at *
    grind only


theorem packedBanks_ok (p : Fin 2) (i j : Fin 8) (len : Nat) (hij : i≠j)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Values} {z : Nat → Int}
    (hv : Banks s v) (hz : ∀e<4,0≤z e ∧ z e<8380417)
    (hzw : ∀e<4,vword (s.v .v28) e=BitVec.ofInt 32 (z e))
    (hbw : ∀e<4,vword (s.v .v29) e=BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀e<4,vword (s.v .v31) e=8380417#32)
    (k : ∀t,VChg (packedClobs (bankRegs p) i j) s t →
      Banks t (fun q => if q=p then Inverse.packedValues (v p) i j len z else v q) →
      WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.packed
      (bankRegs p)[i.val] (bankRegs p)[j.val] len++rest)) s Q := by
  refine packedBank_ok (bankRegs p) i j len hij (bankRegs_inj p) (bankRegs_safe p)
    (hv p) hz hzw hbw hqw fun t hc ht => ?_
  exact k t hc (hv.packed p i j len z hc ht)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
