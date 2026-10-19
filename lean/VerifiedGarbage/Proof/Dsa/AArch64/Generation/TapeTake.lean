module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! # Advance a tape and retain the exact selected chunk address -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem tapeTake_ok (slots : TapeSlots) {s : State} {B base : Addr} {Z used width : Nat}
    (hs : Scr s B Z) (hsp : s.sp = B)
    (hb : 8 * slots.base + 8 ≤ Z) (hu : 8 * slots.used + 8 ≤ Z)
    (hp : 8 * slots.pointer + 8 ≤ Z)
    (hib : 8 * slots.base < 32768) (hiu : 8 * slots.used < 4096)
    (hip : 8 * slots.pointer < 4096) (hwidth : width < 65536)
    (hwb : word s.mem B (8 * slots.base) = base)
    (hwu : word s.mem B (8 * slots.used) = BitVec.ofNat 64 used) :
    WP isa (.block (tapeTake slots width)) s fun t =>
      t.mem = (s.mem.writeW (off B (8 * slots.pointer)) (base + BitVec.ofNat 64 used)).writeW
        (off B (8 * slots.used)) (BitVec.ofNat 64 (used + width)) ∧
      Keep [.x3, .x4, .x5, .x15] s t := by
  have himm : (BitVec.ofNat 16 width).setWidth 64 = BitVec.ofNat 64 width := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  refine WP.keep [.x3, .x4, .x5, .x15] (Q := fun t =>
    t.mem = (s.mem.writeW (off B (8 * slots.pointer)) (base + BitVec.ofNat 64 used)).writeW
      (off B (8 * slots.used)) (BitVec.ofNat 64 (used + width))) ?_ rfl rfl rfl
  unfold tapeTake Impl.Dsa.AArch64.Random.store
  brun [exec_ldrSp ⟨by omega, hib⟩, exec_ldrSp (off := 8 * slots.used) ⟨by omega, by omega⟩,
    exec_addSp hiu, exec_addSp hip, hsp, hs.ld hb, hs.ld hu, hs.st hp, hs.st hu,
    hwb, hwu, himm, ← BitVec.ofNat_add]

end VG.Proof.Dsa.AArch64.Generation
