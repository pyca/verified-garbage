module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectScan
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Frame
import VerifiedGarbage.Proof.Framework.Omega

/-! The packed immutable context lies outside the existing Montgomery workspace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem selectEnv_good {s : State} {B table : Addr} {Z w : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w)
 (readSource : ∀ j<32, ∀ i<w, InRegions (s.rd++s.wr) (off table (8*w*j+8*i)) 8)
 (sourceOutside : ∀ j<32, ∀ i<w, ∀ b<8, Z≤ofs B (off table (8*w*j+8*i)+BitVec.ofNat 64 b)) :
 SelectEnv B table (off B (slot w 5)) w s := by
 have arrayRoom : slot w 5+8*(w+2)≤Z := Nat.le_trans (slot_le (by decide : 5<8)) room
 have size : Z≤2^64 := by have := good.scr.nowrap;omega
 have hd : slot w 5<2^64 := by omega
 have fit : slot w 5+8*w≤2^64 := by omega
 refine ⟨good.x0,good.hdr.harr 5 (by decide),good.hdr.hw,?_,?_,readSource,?_,?_,?_,?_,?_⟩
 · exact good.scr.ld (by have := hdr_lt_slot w 8 (show sArr 5<32 by decide);omega)
 · exact good.scr.ld (by have := hdr_lt_slot w 8 (show sW<32 by decide);omega)
 · intro i hi
   rw [off_off]
   exact good.scr.ld (by omega)
 · intro i hi
   rw [off_off]
   exact good.scr.st (by omega)
 · intro j hj i hi b hb
   exact (outside_shift_iff B _ hd fit).mp (Or.inr (by have := sourceOutside j hj i hi b hb;omega))
 · intro b hb
   apply (outside_shift_iff B _ hd fit).mp
   left
   rw [ofs_off B (by have := hdr_lt_slot w 5 (show sArr 5<32 by decide);omega)]
   have := hdr_lt_slot w 5 (show sArr 5<32 by decide)
   omega
 · intro b hb
   apply (outside_shift_iff B _ hd fit).mp
   left
   rw [ofs_off B (by have := hdr_lt_slot w 5 (show sW<32 by decide);omega)]
   have := hdr_lt_slot w 5 (show sW<32 by decide)
   omega

end VG.Proof.Ffdh.AArch64.Cached
