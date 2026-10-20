module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # Return the primality result to the persistent generation frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Proof.RsaOaep.AArch64

theorem primeResult_ok {s : State} {B F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    {used status : BitVec 64} (L : Lay s F S) (R : Rep s.mem F S V W)
    (hdi : s.gpr .x0 = B)
    (hrused : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off B 216) 8)
    (hrstatus : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off B 248) 8)
    (hu : VG.Proof.Bignum.word s.mem B 216 = used) (hs : VG.Proof.Bignum.word s.mem B 248 = status)
    (hsep : Mem.Sep (VG.Proof.Bignum.off B 248) 8 (VG.Proof.Bignum.off F 128) 8) :
    WP isa (.block Impl.Dsa.AArch64.Generation.primeResult) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 16 used) 19 status) ∧
      Outside F 128 32 s.mem t.mem ∧ Keep [.x3] s t := by
  have hread : (s.mem.writeW (VG.Proof.Bignum.off F 128) used).readW (VG.Proof.Bignum.off B 248) 64 = status := by
    rw [Mem.readW_writeW_sep hsep (by decide)]
    exact hs
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = (s.mem.writeW (VG.Proof.Bignum.off F 128) used).writeW (VG.Proof.Bignum.off F 152) status) (by
    brun [State.write, VG.Proof.RsaOaep.AArch64.off, Impl.Dsa.AArch64.Generation.primeResult, L.sp, hdi,
      hdr_enc (by decide : 27 < 32), hdr_enc (by decide : 31 < 32),
      exec_storeSp (off := 128) (by decide), exec_storeSp (off := 152) (by decide),
      hrused, hrstatus, hu, hread,
      L.st (d := 128) (n := 8) (by decide), L.st (d := 152) (n := 8) (by decide)]) rfl rfl rfl)
    fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd (upd W 16 used) 19 status) := by
    rw [hm]
    exact (R.wf L.geo (by decide : 16 < nW) used).wf
      L.geo (by decide : 19 < nW) status
  refine ⟨lay_of_rep L R Rt (by simp [upd]) hk.sp hk.wr, Rt, ?_, hk⟩
  rw [hm]
  exact ((writeW_outside _ F _ (d := 128) (by decide)).mono (by decide) (by decide)).trans
    ((writeW_outside _ F _ (d := 152) (by decide)).mono (by decide) (by decide))

end VG.Proof.Dsa.AArch64.Generation
