module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LowOrOne
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! The native low-bit update touches exactly one limb of the comparison copy. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem setLowBit_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) :
 WP isa (.block [ldh .x8 (sArr 1),ld .x3 .x8,movi .x4 1,.logic .orr .x .x3 .x3 .x4,st .x3 .x8]) s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 1) w=2*(wv s.mem B (slot w 1) w/2)+1 ∧
 Arrays B w [1] s.mem t.mem ∧ Keep [.x3,.x4,.x8] s t := by
 have arrayRoom := Nat.le_trans (slot_le (w:=w) (show 1<8 by decide)) room
 refine WP.mono (WP.keep [.x3,.x4,.x8] (Q:=fun t =>
  t.mem=s.mem.writeW (off B (slot w 1)) (word s.mem B (slot w 1) ||| 1#64)) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sArr 1<32 by decide),header_read good room (show sArr 1<32 by decide),
    good.hdr.harr 1 (by decide),good.scr.ld (d:=slot w 1) (by omega),good.scr.st (d:=slot w 1) (by omega)]
   rfl
 · rintro t ⟨mem,rest⟩
   have frame : Arrays B w [1] s.mem t.mem := by
    apply Arrays.of_outside (j:=1) (by simp) (o:=slot w 1) (n:=8)
    · rw [mem];exact writeW_outside _ _ _ (by have := good.scr.nowrap;omega)
    · omega
    · have := good.scr.nowrap;omega
   refine ⟨good_after_arrays good frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   rw [mem]
   exact wv_low_or_one _ _ positive (by have := good.scr.nowrap;omega)

end VG.Proof.Ffdh.AArch64.Cached
