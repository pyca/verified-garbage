module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.DrawCopy
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Framework.Omega

/-! Advance the entropy cursor exactly once before copying the draw's suffix. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

theorem drawCopyArgs_ok {s : State} {B rp op : Addr} {Z w used len drawBytes : Nat}
    (h : Ws s B Z w) (hlen : len ≤ drawBytes) (hmax : drawBytes < 4096)
    (hp : word s.mem B (8 * kRand) = rp)
    (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used)
    (ho : word s.mem B (8 * kOut) = op) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.drawCopyArgs len drawBytes)) s fun t =>
      t.gpr .x17 = B ∧ t.gpr .x12 = rp + BitVec.ofNat 64 (used + (drawBytes - len)) ∧
      t.gpr .x2 = op ∧ t.gpr .x9 = BitVec.ofNat 64 len ∧
      t.mem = s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes)) ∧
      Keep [.x2, .x3, .x9, .x12, .x17] s t := by
  refine WP.mono (WP.keep [.x2, .x3, .x9, .x12, .x17] (Q := fun t =>
    t.gpr .x17 = B ∧ t.gpr .x12 = rp + BitVec.ofNat 64 (used + (drawBytes - len)) ∧
    t.gpr .x2 = op ∧ t.gpr .x9 = BitVec.ofNat 64 len ∧
    t.mem = s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (used + drawBytes))) ?_ rfl rfl rfl)
    fun t ⟨ht, hk⟩ => ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2, hk⟩
  have hz := h.scr.nowrap
  have h256 := h.h256
  have hout (v : BitVec 64) : (s.mem.writeW (off B (8 * kUsed)) v).readW (off B (8 * kOut)) 64 = op :=
    ((writeW_outside _ B v (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega)).word
      (by decide) (by simp only [kOut, sFn]; omega)).trans ho
  unfold Impl.Dsa.AArch64.Generation.drawCopyArgs
  brun [h.x0, hdr_enc (show kRand < 32 by decide), hdr_enc (show kUsed < 32 by decide),
    hdr_enc (show kOut < 32 by decide), hp, hu, hout,
    h.scr.ld (d := 8 * kRand) (by simp only [kRand, sFn]; omega),
    h.scr.ld (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega),
    h.scr.ld (d := 8 * kOut) (by simp only [kOut, sFn]; omega),
    h.scr.st (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega),
    hmax, show drawBytes - len < 4096 by omega]
  simp only [BitVec.ofNat_add_ofNat]
  have hv : (BitVec.ofNat 16 len).setWidth 64 = BitVec.ofNat 64 len := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  simp [hv]

end VG.Proof.Dsa.AArch64.Generation
