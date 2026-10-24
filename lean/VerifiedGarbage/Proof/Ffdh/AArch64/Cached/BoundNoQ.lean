module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Copy
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LowDecrement
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! For domains without q the rejection bound is p−1, with no propagated borrow. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem boundNoQ_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (size : w<2^31)
 (odd : wv s.mem B (slot w 0) w%2=1) :
 WP isa (.seq (copy 5 0) (.block [ldh .x8 (sArr 5),ld .x3 .x8,.subImm .x .x3 .x3 1,st .x3 .x8])) s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 5) w=wv s.mem B (slot w 0) w-1 ∧
 Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
 rw [WP.seq_iff]
 refine WP.mono (copy_ok good room positive size (by decide : 5<8) (by decide : 0<8) (by decide)) ?_
 rintro a ⟨goodA,valueA,frameA,restA⟩
 have arrayRoom := Nat.le_trans (slot_le (w:=w) (show 5<8 by decide)) room
 refine WP.mono (WP.keep [.x8,.x3] (Q:=fun t =>t.mem=a.mem.writeW (off B (slot w 5)) (word a.mem B (slot w 5)-1#64)) ?_ rfl rfl rfl) ?_
 · brun [goodA.x0,hdr_enc (show sArr 5<32 by decide),header_read goodA room (show sArr 5<32 by decide),
    goodA.hdr.harr 5 (by decide),goodA.scr.ld (d:=slot w 5) (by omega),goodA.scr.st (d:=slot w 5) (by omega)]
 · rintro t ⟨memT,restT⟩
   have nowrap : slot w 5+8*w≤2^64 := by have := goodA.scr.nowrap;omega
   have value : wv t.mem B (slot w 5) w=wv s.mem B (slot w 0) w-1 := by
    rw [memT,wv_low_decrement _ _ positive nowrap (by rw [valueA];exact odd),valueA]
   have frameT : Arrays B w [5] a.mem t.mem := by
    apply Arrays.of_outside (j:=5) (by simp) (o:=slot w 5) (n:=8)
    · rw [memT];exact writeW_outside _ _ _ (by omega)
    · omega
    · omega
   have rest : Keep mmRegs s t := (restA.trans restT).mono (by simp [mmRegs])
   exact ⟨good_after_arrays goodA frameT restT ((restT.gpr .x0 (by decide)).trans goodA.x0),
    value,frameA.trans frameT,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
