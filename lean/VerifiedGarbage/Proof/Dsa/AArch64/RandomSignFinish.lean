module

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignZero
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublish
public import Mathlib.Data.Int.GCD
public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! All exits clear failed output, wipe the nonce, and publish consumption. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_zero_preserves_word {s t : State} {B op : Addr} {k d : Nat}
    (hf : ∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x)
    (hsep : Mem.Sep (off B d) 8 op k) (hk : k < 2 ^ 64) :
    word t.mem B d = word s.mem B d := by
  apply Mem.readW_congr
  intro i hi
  apply hf
  intro j hj he
  have hleft : ((off B d + BitVec.ofNat 64 i) - off B d).toNat < 8 := by
    rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hi
  have hright : ((off B d + BitVec.ofNat 64 i) - op).toNat < k := by
    rw [he, Mem.sub_ofNat_toNat _ (by omega)]; exact hj
  exact hsep _ hleft hright

/-- The intermediate memory records whether output clearing was required;
the final exact memory expression includes both nonce wiping and publication. -/
theorem random_finish_ok {s : State} {B op : Addr} {k : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hO : word s.mem B Random.oOut = op) (hK : word s.mem B Random.oOutLen = BitVec.ofNat 64 k)
    (hk1 : 0 < k) (hk : k < 2 ^ 64)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hdis : ∀ d, d + 8 ≤ Random.frameBytes → Mem.Sep (off B d) 8 op k)
    (hw : InRegions s.wr (word s.mem B Random.oUsedPtr) 8)
    (hsep : Mem.Sep (off B Random.oStatus) 8 (word s.mem B Random.oUsedPtr) 8) :
    WP isa RandomSign.finish s fun t =>
      t.gpr .x0 = word s.mem B Random.oStatus ∧
      (∃ m : Mem,
        (word s.mem B Random.oStatus = 1 → m = s.mem) ∧
        (word s.mem B Random.oStatus ≠ 1 → ∀ i < k, m (op + BitVec.ofNat 64 i) = 0) ∧
        (∀ d, d + 8 ≤ Random.frameBytes → word m B d = word s.mem B d) ∧
        t.mem = randomPublishMem m B) ∧
      Keep [.x0, .x2, .x4, .x12, .x9, .x15] s t := by
  unfold RandomSign.finish
  refine WP.seq (WP.mono (WP.keep [.x0, .x4] (Q := fun u =>
      u.mem = s.mem ∧ (u.gpr .x4 == 0#64) = (word s.mem B Random.oStatus == 1)) (by
        unfold Random.statusTest
        brun [exec_ldrSp (show Random.oStatus % 8 = 0 ∧ Random.oStatus < 32768 by decide),
          hsp, hs.ld (d := Random.oStatus) (by decide)]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
        rfl) rfl rfl rfl)
    fun u ⟨⟨hum, huz⟩, hku⟩ => ?_)
  have hus := hs.congr hku.wr
  have husp := hku.sp.trans hsp
  have next (v : State) (hkv : Keep [.x0, .x12, .x9] u v)
      (hwords : ∀ d, d + 8 ≤ Random.frameBytes → word v.mem B d = word s.mem B d)
      (hgood : word s.mem B Random.oStatus = 1 → v.mem = s.mem)
      (hbad : word s.mem B Random.oStatus ≠ 1 → ∀ i < k, v.mem (op + BitVec.ofNat 64 i) = 0) :
      WP isa (.block (Random.clearNonce ++
        ([.ldrSp .x2 Random.oUsedPtr, .ldrSp .x0 Random.oUsed,
         .str .x .x0 .x2 0, .ldrSp .x0 Random.oStatus] : List Instr))) v
        (fun t => t.gpr .x0 = word s.mem B Random.oStatus ∧
          (∃ m : Mem, (word s.mem B Random.oStatus = 1 → m = s.mem) ∧
            (word s.mem B Random.oStatus ≠ 1 → ∀ i < k, m (op + BitVec.ofNat 64 i) = 0) ∧
            (∀ d, d + 8 ≤ Random.frameBytes → word m B d = word s.mem B d) ∧
            t.mem = randomPublishMem m B) ∧ Keep [.x0, .x2, .x4, .x12, .x9, .x15] s t) := by
    have hvs := hus.congr hkv.wr
    have hvsp := hkv.sp.trans husp
    have hvp := hwords Random.oUsedPtr (by decide)
    refine WP.mono (random_publish_ok hvs hvsp
      (by rw [hvp, hkv.wr, hku.wr]; exact hw) (by rw [hvp]; exact hsep))
      fun t ⟨hta, htm, hkt⟩ => ?_
    exact ⟨hta.trans (hwords _ (by decide)), ⟨v.mem, hgood, hbad, hwords, htm⟩,
      ((hku.trans hkv).trans hkt).mono (by decide)⟩
  refine WP.seq ?_
  by_cases h1 : word s.mem B Random.oStatus = 1
  · refine WP.ite false (by
      change some (!(u.gpr .x4 == 0#64)) = some false
      rw [huz, h1, BEq.rfl]; rfl)
      (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
    exact next u (Keep.refl _ _) (fun _ _ => by rw [hum]) (fun _ => hum) (fun h => False.elim (h h1))
  · have hz : (word s.mem B Random.oStatus == 1) = false := beq_eq_false_iff_ne.mpr h1
    refine WP.ite true (by
      change some (!(u.gpr .x4 == 0#64)) = some true
      rw [huz, hz]; rfl)
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (random_zeroOut_ok (op := op) (k := k) hus husp (by rw [hum]; exact hO) (by rw [hum]; exact hK)
      hk1 hk (fun j hj => by rw [hku.wr]; exact hout j hj)) fun v ⟨hzero, hf, hkv⟩ => ?_
    exact next v (hkv.mono (by decide))
      (fun d hd => (random_zero_preserves_word hf (hdis d hd) hk).trans (by rw [hum]))
      (fun h => False.elim (h1 h)) (fun _ => hzero)

end VG.Proof.Dsa.AArch64
