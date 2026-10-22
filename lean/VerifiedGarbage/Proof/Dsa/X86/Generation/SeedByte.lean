module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.SeedAdd
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Wp

/-! # One seed byte propagates the exact arithmetic carry -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem seed_add_byte {s : State} {src dst : BitVec 32} {i carry : Nat} {b : Byte}
    (hc : carry < 2 ^ 31) (srcFit : src.toNat + i < 2 ^ 32) (dstFit : dst.toNat + i < 2 ^ 32)
    (source : s.gpr .esi = src) (dest : s.gpr .ebx = dst) (value : s.gpr .edx = BitVec.ofNat 32 carry)
    (read : InRegions (s.rd ++ s.wr) (off (byteAddr src) i) 1)
    (write : InRegions s.wr (off (byteAddr dst) i) 1) (byte : s.mem (off (byteAddr src) i) = b) :
    WP isa (.block (seedAddByte i)) s fun t =>
      t.gpr .edx = BitVec.ofNat 32 ((b.toNat + carry) / 256) ∧
      t.mem = s.mem.writeW (off (byteAddr dst) i) (BitVec.ofNat 8 (b.toNat + carry)) ∧
      Keeps [.eax, .edx] s t := by
  have address : s.ea (at_ .esi i) = off (byteAddr src) i := by
    change byteAddr (s.gpr .esi + BitVec.ofNat 32 i) = _
    rw [source]
    exact byteAddr_add srcFit
  unfold seedAddByte
  refine wp_loadByte address read fun u U => wp_addS rfl fun v V _ => wp_movS rfl fun z Z _ => ?_
  have sum : v.gpr .edx = BitVec.ofNat 32 (b.toNat + carry) := by
    rw [V.gpr, U.other .edx (by decide), value, U.gpr, byte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    have hb := b.isLt
    omega
  refine wp_storeByte (a := off (byteAddr dst) i) ?_ (by rw [Z.wr, V.wr, U.wr]; exact write) fun q Q =>
    wp_shr (by decide) fun t T _ => WP.block_nil ?_
  · change byteAddr (z.gpr .ebx + BitVec.ofNat 32 i) = _
    rw [Z.other .ebx (by decide), V.other .ebx (by decide), U.other .ebx (by decide), dest]
    exact byteAddr_add dstFit
  · refine ⟨?_, ?_, ((((U.keeps.mono (by decide)).trans (V.keeps.mono (by decide))).trans
      (Z.keeps.mono (by decide))).trans (Q.keeps _)).trans (T.keeps.mono (by decide))⟩
    · rw [T.gpr, congrFun Q.gpr .edx, Z.other .edx (by decide), sum]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      have hb := b.isLt
      omega
    · rw [T.mem, Q.mem]
      change z.mem.writeW (off (byteAddr dst) i) ((z.gpr .eax).setWidth 8) = _
      rw [Z.gpr, sum, Z.mem, V.mem, U.mem]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 2 ^ 32)]

end VG.Proof.Dsa.X86.Generation
