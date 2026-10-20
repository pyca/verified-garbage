module
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Impl.MlKem.AArch64.Rej8
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit

import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Value
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Parse

/-! # Rejection shuffle-table contents and selected halfwords -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Impl.MlKem.AArch64.Rej8
open VG.Proof.MlKem.AArch64 VG.Proof.MlKem.AArch64.Ntt16

def tableVec (mask : Nat) : BitVec 128 :=
  ofVDwords (tableWord mask 0) (tableWord mask 1)

theorem tableVec_byte {mask e : Nat} (hm : mask < 256) (he : e < 16) :
    (vbyte (tableVec mask) e).toNat =
      if e/2 < (acceptedLanes mask).length then
        2 * (acceptedLanes mask).getD (e/2) 0 + e%2 else 255 := by
  have finite : ∀ mask < 256, ∀ e < 16, (vbyte (tableVec mask) e).toNat =
      if e/2 < (acceptedLanes mask).length then
        2 * (acceptedLanes mask).getD (e/2) 0 + e%2 else 255 := by decide +kernel
  exact finite mask hm e he

/-- The byte table never selects a candidate outside the loaded vector. -/
theorem accepted_get_bound {mask i : Nat} (hi : i < (acceptedLanes mask).length) :
    (acceptedLanes mask).getD i 0 < 8 := by
  have h := accepted_mem (List.getElem_mem hi)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h

def compactValue (x : BitVec 128) (mask : Nat) : BitVec 128 :=
  ofVBytes fun e =>
    let i := (vbyte (tableVec mask) e).toNat
    if i < 16 then vbyte x i else 0

/-- Table lookup produces the exact stable compaction of the accepted
halfwords, followed by zero lanes. -/
theorem compact_half (x : BitVec 128) {mask e : Nat} (hm : mask < 256) (he : e < 8) :
    vhalf (compactValue x mask) e =
      if e < (acceptedLanes mask).length then vhalf x ((acceptedLanes mask).getD e 0) else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_vhalf _ _ hi]
  rw [show 16*e+i = 8*(2*e+i/8)+i%8 by omega]
  rw [compactValue, getLsbD_ofVBytes _ (by omega) (by omega), tableVec_byte hm (by omega)]
  have hdiv : (2*e+i/8)/2=e := by omega
  have hmod : (2*e+i/8)%2=i/8 := by omega
  rw [hdiv,hmod]
  by_cases ha : e < (acceptedLanes mask).length
  · rw [ite_eq_left ha,ite_eq_left ha]
    have hk := accepted_get_bound ha
    rw [ite_eq_left (by omega)]
    simp only [vbyte, BitVec.getLsbD_extractLsb', show i%8<8 by omega,
      decide_true, Bool.true_and, getLsbD_vhalf _ _ hi]
    exact congrArg _ (by omega)
  · rw [ite_eq_right ha,ite_eq_right ha,ite_eq_right (by decide)]
    simp


end VG.Proof.MlKem.AArch64.Rej8
