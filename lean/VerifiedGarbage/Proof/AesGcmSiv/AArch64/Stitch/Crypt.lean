module

public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Stitch.Loops
public import VerifiedGarbage.Proof.AesGcmSiv.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-GCM-SIV on AArch64, eight blocks at a time: counter mode

Untrusted: everything here is checked by Lean. The keystream of the loops
(`Ctx.ks`) is that of RFC 8452 §4 (`ks_eq`): the counter blocks `cv q` the
loops build are `counterBlock icb q` when the counter block at `W + 96` is
`icb` (`st_cv`). So what `ctrLoop` leaves is counter mode of the batches
(`ctrPart_of_dataInv`), and the blocks after them go as in
`Proof.AesGcmSiv.AArch64.crypt_ok` (`blocksFrom_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.AArch64.Stitch

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcmSiv.AArch64 (Prm Lay Env Perm envRegs CtrSt)
open VG.Proof.Aes.AArch64 (DataInv)
open VG.Proof.Aes.AArch64.Aese (st st_ext getD_st vbyte_readW)

/-! ## The counter blocks -/

theorem vbyte_setLane32_0 (x : BitVec 128) (w : BitVec 32) {j : Nat} (hj : j < 16) :
    vbyte (setLane x 32 0 w) j = if j < 4 then w.extractLsb' (8 * j) 8 else vbyte x j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : j < 4
  · rw [ite_eq_left h]
    simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.sub_zero, show 8 * j + i < 128 by omega,
      show 8 * j + i < 32 by omega, show ¬ 8 * j + i < 0 by omega]
    simp
  · rw [ite_eq_right h]
    simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
      hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.sub_zero, show 8 * j + i < 128 by omega,
      show ¬ 8 * j + i < 32 by omega, show ¬ 8 * j + i < 0 by omega]
    simp [BitVec.getLsbD_of_ge w (8 * j + i) (by omega)]

/-- The loops' counter block `q` is RFC 8452's, of the counter block at `W + 96`. -/
theorem st_cv {σ : Ctx} {icb : List Byte} (C : CtrSt σ.W icb 0 σ.m₀) (q : Nat) :
    st (σ.cv q) = Vector.ofFn fun k => (Spec.GcmSiv.counterBlock icb q).getD k 0 := by
  refine st_ext fun k hk => ?_
  rw [getD_st _ hk, Proof.Aes.AArch64.Aese.getD_ofFn hk, Ctx.cv, vbyte_setLane32_0 _ _ hk,
    GcmSiv.counterBlock_word]
  dsimp only
  have hw : σ.c0 + BitVec.ofNat 32 q = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + q) := by
    show σ.m₀.readW (σ.W + BitVec.ofNat 64 96) 32 + _ = _
    rw [C.word, Nat.add_zero, ← BitVec.ofNat_add]
  by_cases h : k < 4
  · rw [ite_eq_left h, hw, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [Proof.Cmac.length_le4]; exact h)]
    simp [Proof.Cmac.le4, h]
  · rw [ite_eq_right h, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [Proof.Cmac.length_le4]; omega), Proof.Cmac.length_le4,
      ← List.getD_eq_getElem?_getD, vbyte_readW _ _ hk, ← C.rest,
      Proof.Cmac.getD_bytesAt _ _ (by omega), Offset.add_add, Offset.add_add, show 100 + (k - 4) = 96 + k by omega]
    rfl

/-- The loops' keystream is RFC 8452's. -/
theorem ks_eq {σ : Ctx} {icb : List Byte} (C : CtrSt σ.W icb 0 σ.m₀) (i : Nat) :
    σ.ks i = (GcmSiv.ksBlock (Spec.GcmSiv.ctxCiph σ.m₀ σ.K σ.nr) icb (i / 16)).getD (i % 16) 0 := by
  simp only [Ctx.ks, GcmSiv.ksBlock, Spec.GcmSiv.ctxCiph, Spec.GcmSiv.aesWith, st_cv C]
  have hi : i % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [List.getD_eq_getElem?_getD, Vector.getElem?_toList, Vector.getElem?_eq_getElem hi, Option.getD_some]
  simp [Vector.getD, hi]

/-- The data after the batches' counter mode: `ctrPart` of it. -/
theorem ctrPart_of_dataInv {σ : Ctx} {icb : List Byte} (C : CtrSt σ.W icb 0 σ.m₀) {m : Mem} {n : Nat}
    {x : List Byte} (hx : bytesAt σ.m₀ σ.D n = x)
    (hd : DataInv σ.m₀ m σ.D (8 * σ.nb) (8 * σ.nb) σ.ks)
    (hf : ∀ q < n, 128 * σ.nb ≤ q → m (σ.D + BitVec.ofNat 64 q) = σ.m₀ (σ.D + BitVec.ofNat 64 q)) :
    bytesAt m σ.D n = GcmSiv.ctrPart (Spec.GcmSiv.ctxCiph σ.m₀ σ.K σ.nr) icb x (128 * σ.nb) := by
  have hxl : x.length = n := by rw [← hx, Proof.AesGcm.AArch64.length_bytesAt]
  refine GcmSiv.ext_getD (by rw [Proof.AesGcm.AArch64.length_bytesAt, GcmSiv.length_ctrPart, hxl]) fun q hq => ?_
  rw [Proof.AesGcm.AArch64.length_bytesAt] at hq
  rw [Proof.Cmac.getD_bytesAt _ _ hq, GcmSiv.getD_ctrPart _ _ _ _ (by rw [hxl]; exact hq), ← hx,
    Proof.Cmac.getD_bytesAt _ _ hq]
  by_cases h : q < 128 * σ.nb
  · rw [ite_eq_left h, hd q (by omega), ite_eq_left (by omega), ks_eq C]
  · rw [ite_eq_right h, hf q hq (by omega)]

end VG.Proof.AesGcmSiv.AArch64.Stitch
