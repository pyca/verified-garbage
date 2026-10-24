module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Reconstruct the native inverse from the imported odd low modulus limb. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem importInverse_ok {s : State} {B : Addr} {Z w : Nat} {old : BitVec 64}
 (good : Good s B Z w old) (room : slot w 8≤Z) (positive : 0<w)
 (odd : wv s.mem B (slot w 0) w%2=1) :
 WP isa (.block ([ldh .x8 (sArr 0),ld .x3 .x8]++minv++[sth .x15 sMinv])) s fun t =>
 ∃ mi,Good t B Z w mi ∧ ((word t.mem B (slot w 0)).toNat*mi.toNat+1)%2^64=0 ∧
 Outside B (8*sMinv) 8 s.mem t.mem ∧ Keep mmRegs s t := by
 have arrayRoom := Nat.le_trans (slot_le (w:=w) (show 0<8 by decide)) room
 have low := wv_mod64 s.mem B (slot w 0) (by omega : 1≤w)
 have lowOdd : (word s.mem B (slot w 0)).toNat%2=1 := by omega
 rw [List.append_assoc,WP.block_append_iff]
 refine WP.mono (WP.keep [.x8,.x3] (Q:=fun a =>a.gpr .x3=word s.mem B (slot w 0) ∧ a.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sArr 0<32 by decide),header_read good room (show sArr 0<32 by decide),
    good.hdr.harr 0 (by decide),good.scr.ld (d:=slot w 0) (by omega)]
 · rintro a ⟨⟨lowA,memA⟩,restA⟩
   rw [WP.block_append_iff]
   refine WP.mono (minv_ok a (by rw [lowA];exact lowOdd)) ?_
   rintro b ⟨inverseB,restB,memB⟩
   rw [lowA] at inverseB
   have total := restA.trans restB
   refine WP.mono (WP.keep [] (Q:=fun t =>t.mem=b.mem.writeW (off B (8*sMinv)) (b.gpr .x15)) ?_ rfl rfl rfl) ?_
   · brun [(total.gpr .x0 (by decide)).trans good.x0,hdr_enc (show sMinv<32 by decide),
      (good.scr.congr total.wr).st (d:=8*sMinv) (by have := hdr_lt_slot w 8 (show sMinv<32 by decide);omega)]
   · rintro t ⟨memT,restT⟩
     have mem : t.mem=s.mem.writeW (off B (8*sMinv)) (b.gpr .x15) := by rw [memT,memB,memA]
     have frame : Outside B (8*sMinv) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by decide)
     have rest : Keep mmRegs s t := (total.trans restT).mono (by simp [mmRegs])
     have fixed (i : Nat) (hi : i<32) (different : i≠sMinv) : word t.mem B (8*i)=word s.mem B (8*i) :=
      header_other frame (by decide) hi different
     refine ⟨b.gpr .x15,⟨good.scr.congr rest.wr,(rest.gpr .x0 (by simp [mmRegs])).trans good.x0,
      (fixed sW (by decide) (by decide)).trans good.hdr.hw,?_,fun i hi =>
       (fixed (sArr i) (by unfold sArr;omega) (by unfold sArr sMinv;omega)).trans (good.hdr.harr i hi)⟩,?_,frame,rest⟩
     · rw [mem,word_writeW_self]
     · rw [frame.word (Or.inr (hdr_lt_slot w 0 (show sMinv<32 by decide)))
        (by have := good.scr.nowrap;omega)]
       exact inverseB

end VG.Proof.Ffdh.AArch64.Cached
