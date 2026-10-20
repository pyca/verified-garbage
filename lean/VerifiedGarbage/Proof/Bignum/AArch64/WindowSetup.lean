module

public import VerifiedGarbage.Impl.Bignum.AArch64.WindowSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSetup
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem start_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.WindowSetup.start) s fun t =>
      (t.gpr .x8 = off B (slot w aAcc+16) ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
       t.gpr .x7 = 0 ∧ t.mem = s.mem) ∧ Keep [.x8,.x12,.x7] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8*i)) 8 :=
    fun i hi => hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.keep [.x8,.x12,.x7] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.WindowSetup.start
  brun [h0,hl (sArr aAcc) (by decide),hl sW (by decide),hH.harr aAcc (by decide),hH.hw]

theorem square_ok {s : State} {B : Addr} {Z w a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (ha : a < 8) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WindowSetup.square a)) s fun t =>
      (t.gpr .x8 = off B (slot w aAcc+16) ∧ t.gpr .x9 = off B (slot w a) ∧
       t.gpr .x12 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep [.x8,.x9,.x12] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8*i)) 8 :=
    fun i hi => hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sa : sArr a < 32 := by unfold sArr; omega
  refine WP.keep [.x8,.x9,.x12] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.WindowSetup.square
  brun [h0,hdr_enc sa,hl (sArr aAcc) (by decide),hl (sArr a) sa,hl sW (by decide),
    hH.harr aAcc (by decide),hH.harr a ha,hH.hw]

theorem product_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.WindowSetup.product) s fun t =>
      (t.gpr .x8 = off B (slot w aAcc+16) ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
       t.mem = s.mem) ∧ Keep [.x8,.x12] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8*i)) 8 :=
    fun i hi => hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.keep [.x8,.x12] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.WindowSetup.product
  brun [h0,hl (sArr aAcc) (by decide),hl sW (by decide),hH.harr aAcc (by decide),hH.hw]

end VG.Proof.Bignum.AArch64.WindowSetup
