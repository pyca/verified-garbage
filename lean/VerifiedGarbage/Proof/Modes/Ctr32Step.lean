module

public import VerifiedGarbage.Impl.Modes.Ctr32
public import VerifiedGarbage.Proof.Modes.Steps
public import VerifiedGarbage.Proof.Modes.Ctr32
import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# The operations of counter mode with `inc₃₂` meet GCM's specification

`ctr32F`: a step of counter mode with GCM's `inc₃₂`, the data block XORed
with the encrypted counter block, and the counter block stepped by `inc₃₂`
(`ctr32Val`, `Ctr32.lean`). `ctr32_computes`: the operations of
`Mode.ctr32` compute it; `ctr32_gcm`: running it over the blocks is
`Spec.Gcm.ctr32`, and leaves `inc₃₂ⁿ` of the counter block. Nothing here
depends on a target.
-/

@[expose] public section

namespace VG.Proof.Modes

open VG VG.Impl.Modes VG.Spec.Cbc
open VG.Spec.Ctr (ofNat toNat)

/-- One counter block, encrypted and XORed with the input, and the counter
block stepped by `inc₃₂`. -/
def ctr32F (ciph : Cipher) : StepFn := fun ctr x => (xor x (ciph ctr), ofNat (ctr32Val (toNat ctr) 1) 16)

/-- `inc₃₂` on bytes: the first 12 bytes, and the last 4 as a big-endian
number plus 1. -/
theorem ofNat_ctr32Val_one (V : Nat) :
    ofNat (ctr32Val V 1) 16 = (ofNat V 16).take 12 ++ ofNat (toNat ((ofNat V 16).drop 12) + 1) 4 := by
  rw [show (16 : Nat) = 12 + 4 from rfl, AesCtr.ofNat_add, AesCtr.ofNat_add,
    List.take_left' (AesCtr.length_ofNat _ _), List.drop_left' (AesCtr.length_ofNat _ _), AesCtr.toNat_ofNat]
  congr 1
  · congr 1
    simp only [ctr32Val, Nat.reducePow]
    omega
  · apply AesCtr.ofNat_congr
    simp only [ctr32Val, Nat.reducePow]
    omega

theorem ctr32_computes {ciph : Cipher} (hc : ∀ b, (ciph b).length = 16) :
    Computes Mode.ctr32 16 ciph (ctr32F ciph) := by
  intro a
  have hb : rd (applyOps (copyBlk 4 .buf .chn) a) .buf 16 = rd a .chn 16 :=
    rd_eq (rd_length _ _ _) fun i hi => by
      rw [copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩, getD_rd hi]
  let b := cryptBuf 16 ciph (applyOps (copyBlk 4 .buf .chn) a)
  have hchn : ∀ i, applyOps (xorBlk 4 .dat .dat .buf) b .chn i = a .chn i := by
    intro i
    rw [xorBlk_apply, ite_eq_right (by simp)]
    simp only [b, cryptBuf, reduceCtorEq, ite_false]
    rw [copyBlk_apply (by decide), ite_eq_right (by simp)]
  have ht : (rd a .chn 16).length = 16 := rd_length _ _ _
  have hnext := ofNat_ctr32Val_one (toNat (rd a .chn 16))
  rw [AesCtr.ofNat_toNat ht] at hnext
  have hlo : (List.range 4).map (fun j => applyOps (xorBlk 4 .dat .dat .buf) b .chn (12 + j)) =
      (rd a .chn 16).drop 12 := by
    apply List.ext_getElem (by simp [rd])
    intro j h1 _
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop, hchn, rd]
  simp only [stepA, Mode.ctr32, ctr32F, applyOps_snoc]
  refine ⟨rd_eq (by simp [xor_length, rd_length, hc]) fun i hi => ?_,
    rd_eq (by rw [hnext]; simp [AesCtr.length_ofNat, ht]) fun i hi => ?_⟩
  · simp only [Op.apply, reduceCtorEq, false_and, ite_false]
    rw [xorBlk_apply, ite_eq_left ⟨rfl, hi⟩]
    simp only [cryptBuf, reduceCtorEq, ite_false, ite_true, hb]
    rw [copyBlk_apply (by decide), ite_eq_right (by simp),
      getD_xor (by rw [rd_length]; exact hi) (by rw [hc]; exact hi), getD_rd hi]
  · rw [hnext]
    simp only [Op.apply, Op.width, Op.val, Bool.false_eq_true, ite_true, ite_false, true_and]
    by_cases h12 : 12 ≤ i
    · rw [ite_eq_left ⟨h12, by omega⟩, hlo, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp; omega)]
      simp only [List.length_take, ht, show min 12 16 = 12 from rfl]
    · rw [ite_eq_right (fun h => h12 h.1), hchn, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp [ht]; omega), ← getD_rd (a := a) (l := .chn) hi, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt (by omega)]

/-- The steps from the counter block `ofNat V 16`: block `j` XORed with the
encryption of the counter block `ctr32Val V j`, and `ctr32Val V n` left. -/
theorem ctr32_run (ciph : Cipher) : ∀ (V : Nat) (xs : List (List Byte)),
    (run (ctr32F ciph) (ofNat V 16) xs).1 =
        (List.range xs.length).map (fun j => xor (xs.getD j []) (ciph (ofNat (ctr32Val V j) 16))) ∧
      (run (ctr32F ciph) (ofNat V 16) xs).2 = ofNat (ctr32Val V xs.length) 16
  | V, [] => ⟨rfl, by rw [List.length_nil, ctr32Val_zero]; rfl⟩
  | V, x :: xs => by
    -- The counter block after the first step, as `ctr32Val V 1` is, modulo 2¹²⁸.
    have hc : ∀ j, ofNat (ctr32Val (ctr32Val (toNat (ofNat V 16)) 1) j) 16 = ofNat (ctr32Val V (j + 1)) 16 :=
      fun j => AesCtr.ofNat_congr (by
        rw [ctr32Val_add, AesCtr.toNat_ofNat]
        simp only [ctr32Val, Nat.reducePow]
        omega)
    obtain ⟨h1, h2⟩ := ctr32_run ciph (ctr32Val (toNat (ofNat V 16)) 1) xs
    simp only [hc] at h1 h2
    refine ⟨?_, ?_⟩
    · simp only [run, ctr32F, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      rw [h1]
      congr 1
      rw [ctr32Val_zero]; rfl
    · simp only [run, ctr32F, List.length_cons]
      rw [h2]

/-- Running the steps over 16-byte blocks from the counter block `t` is
GCM's counter mode with `inc₃₂`, and leaves `inc₃₂ⁿ(t)`. -/
theorem ctr32_gcm {ciph : Cipher} (hc : ∀ b, (ciph b).length = 16) {t : List Byte} (ht : t.length = 16)
    {xs : List (List Byte)} (hx : ∀ x ∈ xs, x.length = 16) :
    (run (ctr32F ciph) t xs).1.map Spec.Gcm.ofBytes =
        Spec.Gcm.ctr32 (onBlocks ciph) (Spec.Gcm.ofBytes t) (xs.map Spec.Gcm.ofBytes) ∧
      Spec.Gcm.ofBytes (run (ctr32F ciph) t xs).2 = Nat.repeat Spec.Gcm.inc32 xs.length (Spec.Gcm.ofBytes t) := by
  obtain ⟨h1, h2⟩ := ctr32_run ciph (toNat t) xs
  rw [AesCtr.ofNat_toNat ht] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [h1, Spec.Gcm.ctr32, List.length_map, Spec.Gcm.keystream]
    apply List.ext_getElem (by simp)
    intro j hj _
    simp only [List.length_map, List.length_range] at hj
    have hxj : xs.getD j [] = xs[j] := by simp [List.getD_eq_getElem?_getD, hj]
    have hctr : Spec.Gcm.toBytes (Nat.repeat Spec.Gcm.inc32 j (Spec.Gcm.ofBytes t)) =
        ofNat (ctr32Val (toNat t) j) 16 := by
      rw [toBytes_eq_ofNat, toNat_repeat_inc32, toNat_ofBytes ht]
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, onBlocks, hctr, hxj]
    exact Ocb.ofBytes_xor (hx _ (List.getElem_mem _)) (hc _)
  · rw [h2]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_repeat_inc32, toNat_ofBytes ht, toNat_ofBytes (AesCtr.length_ofNat _ _), AesCtr.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa using ctr32Val_lt (AesCtr.toNat_lt ht) xs.length)]

end VG.Proof.Modes
