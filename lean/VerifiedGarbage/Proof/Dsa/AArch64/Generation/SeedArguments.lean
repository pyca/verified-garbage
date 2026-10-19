module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.Omega

/-! # Bind each complete seed to q hashing without resetting witness consumption -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def seedWords (W : Nat → BitVec 64) (len : Nat) : Nat → BitVec 64 :=
  upd (upd (upd W 0 (VG.Proof.Bignum.off (W 5) q)) 25 (W 1)) 26 (BitVec.ofNat 64 len)

theorem seedArguments_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {len : Nat} (hl : len < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.seedArguments len)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (seedWords W len) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  have cast : (BitVec.ofNat 16 len).setWidth 64 = BitVec.ofNat 64 len := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have read : (s.mem.writeW (VG.Proof.Bignum.off F 0) (VG.Proof.Bignum.off (W 5) q)).readW (VG.Proof.Bignum.off F 8) 64 = W 1 := by
    change VG.Proof.Bignum.word (s.mem.writeW (VG.Proof.Bignum.off F 0) (VG.Proof.Bignum.off (W 5) q)) F 8 = W 1
    rw [(VG.Proof.Bignum.writeW_outside _ F _ (d := 0) (by decide)).word
      (d := 8) (Or.inr (by decide)) (by decide)]
    exact R.fr 1 (by decide)
  simp only [VG.Proof.Bignum.off, BitVec.add_zero] at read
  have st0 : InRegions s.wr F 8 := by simpa [VG.Proof.Bignum.off] using L.st (d := 0) (n := 8) (by decide)
  have hw : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
  have hq : (BitVec.ofNat 16 q).setWidth 64 = BitVec.ofNat 64 q := by decide
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
      t.mem = ((s.mem.writeW (VG.Proof.Bignum.off F 0) (VG.Proof.Bignum.off (W 5) q)).writeW (VG.Proof.Bignum.off F 200) (W 1)).writeW
        (VG.Proof.Bignum.off F 208) (BitVec.ofNat 64 len)) (by
    brun [State.write, Impl.Dsa.AArch64.Generation.seedArguments, sLab, sLabLen,
      exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 8) (by decide),
      exec_storeSp (off := 0) (by decide), exec_storeSp (off := 200) (by decide),
      exec_storeSp (off := 208) (by decide), L.sp, BitVec.add_zero,
      L.ld (d := 40) (n := 8) (by decide), L.ld (d := 8) (n := 8) (by decide),
      st0, L.st (d := 200) (n := 8) (by decide), L.st (d := 208) (n := 8) (by decide),
      hw, hq, cast, read, VG.Proof.Bignum.off]) rfl rfl rfl)
    fun t ⟨hm, kt⟩ => ?_
  have Rt : Rep t.mem F S V (seedWords W len) := by
    rw [hm]
    exact ((R.wf L.geo (by decide : 0 < nW) _).wf L.geo (by decide : 25 < nW) _).wf L.geo (by decide : 26 < nW) _
  refine ⟨lay_of_rep L R Rt (by simp [seedWords, upd]) kt.sp kt.wr, Rt, ?_, kt⟩
  have ff : Outside F 0 frameBytes s.mem t.mem := by
    rw [hm]
    exact (((writeW_outside _ F _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ F _ (d := 200) (by decide)).mono (by decide) (by decide))).trans
      ((writeW_outside _ F _ (d := 208) (by decide)).mono (by decide) (by decide))
  intro a ha
  apply ff a
  right
  have hn := ha ⟨F, frameBytes⟩ (by simp)
  change ¬ ofs F a < frameBytes at hn
  omega

end VG.Proof.Dsa.AArch64.Generation
