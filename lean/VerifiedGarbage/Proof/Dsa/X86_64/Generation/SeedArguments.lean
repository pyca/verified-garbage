module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Omega

/-! # Bind each complete seed to q hashing without resetting witness consumption -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def seedWords (W : Nat → BitVec 64) (len : Nat) : Nat → BitVec 64 :=
  upd (upd (upd W 0 (off (W 5) q)) 27 (W 1)) 28 (BitVec.ofNat 64 len)

theorem seedArguments_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {len : Nat} (hl : len < 2 ^ 32) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.seedArguments len)) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (seedWords W len) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  have cast : (BitVec.ofNat 32 len).setWidth 64 = BitVec.ofNat 64 len := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
  have read : (s.mem.writeW (off F 0) (off (W 5) q)).readW (off F 8) 64 = W 1 := by
    exact (R.wf L.geo (by decide : 0 < nW) _).slot (d := 8) (k := 1) rfl (by decide) (by simp [upd])
  have st0 : InRegions s.wr F 8 := by simpa [off] using L.st (d := 0) (by decide)
  have read0 : (s.mem.writeW F (off (W 5) q)).readW (off F 8) 64 = W 1 := by simpa [off] using read
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = ((s.mem.writeW (off F 0) (off (W 5) q)).writeW (off F 216) (W 1)).writeW
        (off F 224) (BitVec.ofNat 64 len)) (by
    xrun [Impl.Dsa.X86_64.Generation.seedArguments, ea_sp, L.rsp,
      L.ld (d := 40) (by decide), R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      L.ld (d := 8) (by decide), st0, L.st (d := 216) (by decide),
      L.st (d := 224) (by decide), sx_ofNat (by decide : q < 2 ^ 31), cast, read0]) rfl)
    fun t ⟨hm, kt⟩ => ?_
  have Rt : Rep t.mem F S V (seedWords W len) := by
    rw [hm]
    exact ((R.wf L.geo (by decide : 0 < nW) _).wf L.geo (by decide : 27 < nW) _).wf L.geo (by decide : 28 < nW) _
  refine ⟨lay_of_rep L R Rt (by simp [seedWords, upd]) (kt.gpr (by decide)) kt.2.2, Rt, ?_, kt⟩
  have ff : Outside F 0 frameBytes s.mem t.mem := by
    rw [hm]
    exact (((writeW_outside _ F _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ F _ (d := 216) (by decide)).mono (by decide) (by decide))).trans
      ((writeW_outside _ F _ (d := 224) (by decide)).mono (by decide) (by decide))
  intro a ha
  apply ff a
  right
  have hn := ha ⟨F, frameBytes⟩ (by simp)
  change ¬ ofs F a < frameBytes at hn
  omega

end VG.Proof.Dsa.X86_64.Generation
