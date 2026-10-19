module
public import VerifiedGarbage.Impl.Bignum.AArch64.WindowSparse
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem shift_four (k : Nat) (hk : k < 2^56) :
    BitVec.ofNat 64 (8*k) <<< 4 = BitVec.ofNat 64 (128*k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show 8*k < 2^64 by omega),BitVec.toNat_ofNat]
  congr 1
  omega

theorem padding_ok {s : State} {B : Addr} {Z e k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B e) (h12 : s.gpr .x12 = BitVec.ofNat 64 (8*k))
    (h7 : s.gpr .x7 = 0) (he : e+128*k+16 ≤ Z) (hk : k < 2^56) :
    WP isa (.block VG.Impl.Bignum.AArch64.WindowSparse.padding) s fun t =>
      wv t.mem B (e+128*k) 2 = 0 ∧ Outside B (e+128*k) 16 s.mem t.mem ∧ Keep [.x14,.x16] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [.x14,.x16] (Q := fun t =>
    t.mem = (s.mem.writeW (off B (e+128*k)) (0 : BitVec 64)).writeW (off B (e+128*k+8)) (0 : BitVec 64))
    ?_ rfl rfl rfl) fun t ⟨hm,kt⟩ => ?_
  · unfold VG.Impl.Bignum.AArch64.WindowSparse.padding
    brun [h8,h12,h7,shift_four k hk,hs.st (show e+128*k+8 ≤ Z by omega),
      hs.st (show e+128*k+8+8 ≤ Z by omega)]
  have ho1 := writeW_outside s.mem B (d := e+128*k) (0 : BitVec 64) (by omega)
  have ho2 := writeW_outside (s.mem.writeW (off B (e+128*k)) (0 : BitVec 64)) B
    (d := e+128*k+8) (0 : BitVec 64) (by omega)
  refine ⟨?_,?_,kt⟩
  · rw [hm]
    apply (wv_eq_zero_iff _ _ _ _).mpr
    intro j hj
    rcases (show j=0 ∨ j=1 by omega) with rfl | rfl
    · rw [show e+128*k+8*0 = e+128*k by omega,ho2.word (by omega) (by omega),word_writeW_self]
    · rw [show e+128*k+8*1 = e+128*k+8 by omega,word_writeW_self]
  · rw [hm]
    exact (ho1.mono (by omega) (by omega)).trans (ho2.mono (by omega) (by omega))

end VG.Proof.Bignum.AArch64.WindowSparse
