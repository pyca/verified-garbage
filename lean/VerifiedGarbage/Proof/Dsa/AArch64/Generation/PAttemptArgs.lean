module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Framework.Omega

/-! # Frame arguments for a complete p-candidate attempt -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Proof.RsaOaep.AArch64

theorem pAttemptArgs_ok {s : State} {B F S op : Addr} {V : Nat → Byte}
    {W : Nat → BitVec 64} {offset : BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hdi : s.gpr .x0 = B)
    (hread : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off B 8) 8)
    (hoff : VG.Proof.Bignum.word s.mem B 8 = offset)
    (hop : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.shaped = op) :
    WP isa (.block Impl.Dsa.AArch64.Generation.pAttemptArgs) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd (upd W 0 op) 2 offset) 25 (W 3)) ∧
      Outside F 0 208 s.mem t.mem ∧ Keep [.x3, .x4, .x5] s t := by
  have hst0 : InRegions s.wr F 8 := by simpa [VG.Proof.Bignum.off] using L.st (d := 0) (n := 8) (by decide)
  have hw5 : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
  have hi : (BitVec.ofNat 16 Impl.Dsa.Generation.Layout.shaped).setWidth 64 =
      BitVec.ofNat 64 Impl.Dsa.Generation.Layout.shaped := by decide
  have hw3 : VG.Proof.Bignum.word ((s.mem.writeW (VG.Proof.Bignum.off F 0) op).writeW (VG.Proof.Bignum.off F 16) offset) F 24 = W 3 := by
    rw [(writeW_outside _ F _ (d := 16) (by decide)).word (Or.inr (by decide)) (by decide),
      (writeW_outside _ F _ (d := 0) (by decide)).word (Or.inr (by decide)) (by decide)]
    exact R.fr 3 (by decide)
  simp only [VG.Proof.Bignum.word, VG.Proof.Bignum.off, BitVec.add_zero] at hw3
  refine WP.mono (WP.keep [.x3, .x4, .x5] (Q := fun t =>
      t.mem = ((s.mem.writeW (VG.Proof.Bignum.off F 0) op).writeW (VG.Proof.Bignum.off F 16) offset).writeW
        (VG.Proof.Bignum.off F 200) (W 3)) (by
    brun [State.write, VG.Impl.RsaOaep.AArch64.sLab,
      VG.Proof.RsaOaep.AArch64.off, VG.Proof.Bignum.off, Impl.Dsa.AArch64.Generation.pAttemptArgs, L.sp, hdi, hread, hoff,
      exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 24) (by decide),
      exec_storeSp (off := 0) (by decide), exec_storeSp (off := 16) (by decide),
      exec_storeSp (off := 200) (by decide), hdr_enc (by decide : 1 < 32),
      L.ld (d := 40) (n := 8) (by decide), L.ld (d := 24) (n := 8) (by decide),
      hst0, L.st (d := 16) (n := 8) (by decide), L.st (d := 200) (n := 8) (by decide),
      hw5, hi, hop, hw3, BitVec.add_zero]) rfl rfl rfl)
    fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd (upd (upd W 0 op) 2 offset) 25 (W 3)) := by
    rw [hm]
    exact ((R.wf L.geo (by decide : 0 < nW) op).wf L.geo
      (by decide : 2 < nW) offset).wf L.geo (by decide : 25 < nW) (W 3)
  refine ⟨lay_of_rep L R Rt (by simp [upd]) hk.sp hk.wr, Rt, ?_, hk⟩
  rw [hm]
  exact (((writeW_outside _ F _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
    ((writeW_outside _ F _ (d := 16) (by decide)).mono (by decide) (by decide))).trans
    ((writeW_outside _ F _ (d := 200) (by decide)).mono (by decide) (by decide))

end VG.Proof.Dsa.AArch64.Generation
