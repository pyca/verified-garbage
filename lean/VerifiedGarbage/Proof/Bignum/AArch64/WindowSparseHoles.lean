module

public import VerifiedGarbage.Impl.Bignum.AArch64.WindowSparse
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem holes_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e) (h7 : s.gpr .x7 = 0)
    (he : e+128 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.WindowSparse.holes) s fun t =>
      word t.mem B e = 0 ∧ word t.mem B (e+120) = 0 ∧
      Outside B e 128 s.mem t.mem ∧ Keep [] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [] (Q := fun t =>
    t.mem = (s.mem.writeW (off B e) (0 : BitVec 64)).writeW (off B (e+120)) (0 : BitVec 64))
    ?_ rfl rfl rfl) fun t ⟨hm,kt⟩ => ?_
  · unfold VG.Impl.Bignum.AArch64.WindowSparse.holes
    brun [h16,h7,hs.st (show e+8 ≤ Z by omega),hs.st (show e+120+8 ≤ Z by omega)]
  · refine ⟨?_,?_,?_,kt⟩
    · rw [hm,(writeW_outside (s.mem.writeW (off B e) (0 : BitVec 64)) B
        (d := e+120) (0 : BitVec 64) (by omega)).word (by omega) (by omega),word_writeW_self]
    · rw [hm,word_writeW_self]
    · rw [hm]
      exact (writeW_outside s.mem B (0 : BitVec 64) (by omega)).mono (by omega) (by omega) |>.trans
        ((writeW_outside (s.mem.writeW (off B e) (0 : BitVec 64)) B (d := e+120)
          (0 : BitVec 64) (by omega)).mono (by omega) (by omega))

end VG.Proof.Bignum.AArch64.WindowSparse
