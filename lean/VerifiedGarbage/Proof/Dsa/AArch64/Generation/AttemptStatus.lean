module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Return a p-attempt result to the bounded search controller -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Proof.RsaOaep.AArch64

theorem stackStatus_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (status : Nat) (hs : status < 2 ^ 16) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.stackStatus status)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 status)) ∧
      Outside F 152 8 s.mem t.mem ∧ Keep [.x3] s t := by
  have hv : (BitVec.ofNat 16 status).setWidth 64 = BitVec.ofNat 64 status := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = s.mem.writeW (VG.Proof.Bignum.off F 152) (BitVec.ofNat 64 status)) (by
    brun [Impl.Dsa.AArch64.Generation.stackStatus, exec_storeSp (off := 152) (by decide),
      L.sp, L.st (d := 152) (n := 8) (by decide), hv]) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 status)) := by
    rw [hm]; exact R.wf L.geo (by decide : 19 < nW) _
  refine ⟨lay_of_rep L R Rt (by simp [upd]) hk.sp hk.wr, Rt, ?_, hk⟩
  rw [hm]; exact writeW_outside _ _ _ (by decide)

theorem controlBase_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hB : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.control = B) :
    WP isa (.block Impl.Dsa.AArch64.Generation.controlBase) s fun t =>
      t.gpr .x0 = B ∧ t.mem = s.mem ∧ Keep [.x0, .x3] s t := by
  refine WP.mono (WP.keep [.x0, .x3] (Q := fun t => t.gpr .x0 = B ∧ t.mem = s.mem) (by
    have hw : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
    brun [Impl.Dsa.AArch64.Generation.controlBase, exec_ldrSp (off := 40) (by decide), L.sp,
      L.ld (d := 40) (n := 8) (by decide), hw]
    exact hB) rfl rfl rfl) fun _ ⟨⟨hb, hm⟩, hk⟩ => ⟨hb, hm, hk⟩

theorem searchReturn_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hB : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.control = B)
    (hout : InRegions s.wr (VG.Proof.Bignum.off B 16) 8) :
    WP isa (.block Impl.Dsa.AArch64.Generation.searchReturn) s fun t =>
      t.gpr .x0 = B ∧ VG.Proof.Bignum.word t.mem B 16 = W 19 ∧
      Outside B 16 8 s.mem t.mem ∧ Keep [.x0, .x3] s t := by
  refine WP.mono (WP.keep [.x0, .x3] (Q := fun t =>
      t.gpr .x0 = B ∧ t.mem = s.mem.writeW (VG.Proof.Bignum.off B 16) (W 19)) (by
    have hw : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
    have hc : (BitVec.ofNat 16 Impl.Dsa.Generation.Layout.control).setWidth 64 =
        BitVec.ofNat 64 Impl.Dsa.Generation.Layout.control := by decide
    have hs : s.mem.readW (F + BitVec.ofNat 64 152) 64 = W 19 := R.fr 19 (by decide)
    brun [Impl.Dsa.AArch64.Generation.searchReturn, Impl.Dsa.AArch64.Generation.controlBase,
      exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 152) (by decide), L.sp,
      L.ld (d := 40) (n := 8) (by decide), L.ld (d := 152) (n := 8) (by decide), hw, hs, hc,
      hdr_enc (by decide : 2 < 32), hB, hout]) rfl rfl rfl)
    fun t ⟨⟨hb, hm⟩, hk⟩ => ?_
  refine ⟨hb, ?_, ?_, hk⟩
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [hm]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Dsa.AArch64.Generation
