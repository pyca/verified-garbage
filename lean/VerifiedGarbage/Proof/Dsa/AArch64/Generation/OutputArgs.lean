module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Prepare accepted-output copying and the existing zero-output loop. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Bignum (Outside writeW_outside)
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem outputArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {len : Nat} (hlen : W 7 = BitVec.ofNat 64 len) :
    WP isa (.block Impl.Dsa.AArch64.Generation.outputArgs) s fun t =>
      t.gpr .x12 = off (W 5) packed ∧ t.gpr .x2 = W 6 ∧
      t.gpr .x9 = BitVec.ofNat 64 len ∧ t.mem = s.mem ∧ Keep [.x12, .x2, .x9, .x3] s t := by
  have h5 : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
  have h6 : s.mem.readW (F + BitVec.ofNat 64 48) 64 = W 6 := R.fr 6 (by decide)
  have h7 : s.mem.readW (F + BitVec.ofNat 64 56) 64 = BitVec.ofNat 64 len := (R.fr 7 (by decide)).trans hlen
  have hc : (BitVec.ofNat 16 packed).setWidth 64 = BitVec.ofNat 64 packed := by decide
  refine WP.mono (WP.keep [.x12, .x2, .x9, .x3] (Q := fun t =>
    t.gpr .x12 = off (W 5) packed ∧ t.gpr .x2 = W 6 ∧
    t.gpr .x9 = BitVec.ofNat 64 len ∧ t.mem = s.mem) (by
    brun [Impl.Dsa.AArch64.Generation.outputArgs,
      exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 48) (by decide),
      exec_ldrSp (off := 56) (by decide), L.sp,
      L.ld (d := 40) (n := 8) (by decide), L.ld (d := 48) (n := 8) (by decide),
      L.ld (d := 56) (n := 8) (by decide), h5, h6, h7, hc]) rfl rfl rfl)
    fun _ ⟨⟨a, b, c, d⟩, hk⟩ => ⟨a, b, c, d, hk⟩

theorem zeroArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block Impl.Dsa.AArch64.Generation.zeroArgs) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 19 (W 6)) 21 (W 7)) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3] s t := by
  have h6 : s.mem.readW (F + BitVec.ofNat 64 48) 64 = W 6 := R.fr 6 (by decide)
  have read : VG.Proof.Bignum.word (s.mem.writeW (off F 152) (W 6)) F 56 = W 7 := by
    rw [(writeW_outside _ F _ (d := 152) (by decide)).word (d := 56) (Or.inl (by decide)) (by decide)]
    exact R.fr 7 (by decide)
  simp only [VG.Proof.Bignum.word, off] at read
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.mem = (s.mem.writeW (off F 152) (W 6)).writeW (off F 168) (W 7)) (by
    brun [State.write, Impl.Dsa.AArch64.Generation.zeroArgs, sOut, sK,
      exec_ldrSp (off := 48) (by decide), exec_ldrSp (off := 56) (by decide),
      exec_storeSp (off := 152) (by decide), exec_storeSp (off := 168) (by decide), L.sp,
      L.ld (d := 48) (n := 8) (by decide), L.ld (d := 56) (n := 8) (by decide),
      L.st (d := 152) (n := 8) (by decide), L.st (d := 168) (n := 8) (by decide), h6, read, off])
    rfl rfl rfl) fun t ⟨hm, kt⟩ => ?_
  have Rt : Rep t.mem F S V (upd (upd W 19 (W 6)) 21 (W 7)) := by
    rw [hm]
    exact (R.wf L.geo (by decide : 19 < nW) _).wf L.geo (by decide : 21 < nW) _
  refine ⟨lay_of_rep L R Rt (by simp [upd]) kt.sp kt.wr, Rt, ?_, kt⟩
  rw [hm]
  exact ((Frame.refl [⟨F, frameBytes⟩] s.mem).writeW (r := ⟨F, frameBytes⟩) (by simp) _
    (Offset.contains_base _ (by decide) (by decide))).writeW (r := ⟨F, frameBytes⟩)
      (by simp) _ (Offset.contains_base _ (by decide) (by decide))

end VG.Proof.Dsa.AArch64.Generation
