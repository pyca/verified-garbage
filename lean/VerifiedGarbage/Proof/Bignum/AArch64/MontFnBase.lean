module

public import VerifiedGarbage.Impl.Bignum.AArch64.MontFn
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.MontFn
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Bignum.AArch64.MontFn

theorem ofNat32_64 {j : Nat} (h : j < 2 ^ 32) :
    (BitVec.ofNat 32 j).setWidth 64 = BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]
  omega

theorem array_addr (B : Addr) {j : Nat} (h : j < 8) :
    B + ((BitVec.ofNat 32 j).setWidth 64 <<< 3) + BitVec.ofNat 64 64 = off B (8 * sArr j) := by
  rw [ofNat32_64 (by omega)]
  simp only [BitVec.add_assoc, off, sArr]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem zext_exec (s : State) (r : Reg) :
    exec (.addImm .w r r 0) s = some (s.write .w r ((s.gpr r).setWidth 32)) := by
  simp [exec, State.read]

theorem head_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (h2 : (s.gpr .x2).setWidth 32 = BitVec.ofNat 32 o)
    (h3 : (s.gpr .x3).setWidth 32 = BitVec.ofNat 32 a)
    (h4 : (s.gpr .x4).setWidth 32 = BitVec.ofNat 32 b) :
    WP isa (.block basesR) s fun t =>
      (t.gpr .x8 = off B (slot w 2) ∧ t.gpr .x9 = off B (slot w b) ∧ t.gpr .x10 = off B (slot w 0) ∧
      t.gpr .x11 = off B (slot w a) ∧ t.gpr .x5 = off B (slot w o) ∧ t.gpr .x6 = off B (slot w 3) ∧
      t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x15 = minv ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧
      VG.Proof.MlKem.AArch64.Keep mmRegs s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  refine WP.keep mmRegs ?_ rfl rfl rfl
  unfold basesR basesTail loadArray zext
  brun [zext_exec, hdr_enc, show 64 % 8 = 0 ∧ 64 < 32768 by decide, BitVec.add_zero, h0, h2, h3, h4,
    array_addr B ho, array_addr B ha, array_addr B hb,
    hl _ (sa o ho), hl _ (sa a ha), hl _ (sa b hb),
    hl _ (sa 2 (by decide)), hl _ (sa 0 (by decide)), hl _ (sa 3 (by decide)),
    hl sW (by decide), hl sMinv (by decide),
    hH.harr o ho, hH.harr a ha, hH.harr b hb,
    hH.harr 0 (by decide), hH.harr 2 (by decide), hH.harr 3 (by decide), hH.hw, hH.hminv]

end VG.Proof.Bignum.AArch64.MontFn
