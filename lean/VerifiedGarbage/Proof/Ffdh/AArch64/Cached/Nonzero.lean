module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
/-! The full scalar nonzero predicate is written as a 0/1 control word. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/NonzeroScan.lean`, which only this module imported.
section

/-! The scalar's nonzero test scans every limb without branching on its value. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure NonzeroInv (s : State) (B : Addr) (e j : Nat) (t : State) : Prop where
 mem : t.mem=s.mem
 keep : Keep [.x3,.x8,.x9,.x12] s t
 pointer : t.gpr .x8=off B (e+8*j)
 value : t.gpr .x9=0#64 ↔ ∀ i<j,word s.mem B (e+8*i)=0#64

theorem nonzeroScanStep_ok {s t : State} {B : Addr} {Z e w j : Nat}
 (scratch : Scr s B Z) (fit : e+8*w≤Z) (inside : j<w) (inv : NonzeroInv s B e j t) :
 WP isa (.block ([ld .x3 .x8,.logic .orr .x .x9 .x9 .x3,next .x8]++([.subImm .x .x12 .x12 1] : List Instr))) t fun u =>
 NonzeroInv s B e (j+1) u ∧ u.gpr .x12=t.gpr .x12-1#64 := by
 rw [WP.block_append_iff]
 refine WP.mono (WP.keep [.x3,.x8,.x9] (Q:=fun a =>a.mem=t.mem ∧
  a.gpr .x9=t.gpr .x9 ||| word t.mem B (e+8*j) ∧ a.gpr .x8=off B (e+8*j+8)) ?_ rfl rfl rfl) ?_
 · brun [inv.pointer,(scratch.congr inv.keep.wr).ld (d:=e+8*j) (by omega)]
 · rintro a ⟨⟨memA,valueA,ptrA⟩,restA⟩
   refine WP.mono (dec_ok a .x12) ?_
   rintro u ⟨⟨count,memU,_⟩,restU⟩
   refine ⟨⟨memU.trans (memA.trans inv.mem),((inv.keep.trans restA).trans restU).mono (by simp),?_,?_⟩,?_⟩
   · rw [restU.gpr .x8 (by decide),ptrA]
     rw [show e+8*j+8=e+8*(j+1) by omega]
   · rw [restU.gpr .x9 (by decide),valueA,BitVec.or_eq_zero_iff,inv.value,inv.mem]
     constructor
     · rintro ⟨low,top⟩ i hi
       rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
       · exact low i hi
       · exact top
     · intro h
       exact ⟨fun i hi =>h i (by omega),h j (by omega)⟩
   · rw [count,restA.gpr .x12 (by decide)]

theorem nonzeroScan_ok {s : State} {B : Addr} {Z e w : Nat}
 (scratch : Scr s B Z) (fit : e+8*w≤Z) (positive : 0<w) (size : w<2^31)
 (pointer : s.gpr .x8=off B e) (zero : s.gpr .x9=0#64) (count : s.gpr .x12=BitVec.ofNat 64 w) :
 WP isa (countLoop .x12 [ld .x3 .x8,.logic .orr .x .x9 .x9 .x3,next .x8]) s fun t =>
 (t.gpr .x9=0#64 ↔ wv s.mem B e w=0) ∧ t.mem=s.mem ∧ Keep [.x3,.x8,.x9,.x12] s t := by
 refine WP.mono (wp_countdown (N:=w) (by omega) (by omega) (NonzeroInv s B e)
  (fun j hj t h _ =>nonzeroScanStep_ok scratch fit hj h) ?_ count) ?_
 · exact ⟨rfl,Keep.refl _ _,by simpa using pointer,by rw [zero];simp⟩
 · intro t h
   refine ⟨?_,h.mem,h.keep⟩
   rw [h.value,wv_eq_zero_iff]
   rfl

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem exec_cselc_x (s : State) (d n m : Reg) (cond : CondCode) :
 exec (.cselc .x d n m cond) s=some (s.write .x d (if cond.holds s then s.gpr n else s.gpr m)) := rfl
private theorem zeroFlag (s : State) (d : Reg) (a b : BitVec 64) (c : Bool) :
 (s.addWithCarry .x d a b c).zf=decide (a+b+BitVec.ofNat 64 c.toNat=0#64) := rfl

theorem nonzero_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (size : w<2^31) :
 WP isa Generate.nonzero s fun t =>
 Good t B Z w mi ∧ t.gpr .x9=(if wv s.mem B (slot w 1) w=0 then 0#64 else 1#64) ∧
 word t.mem B (8*sTmp)=(if wv s.mem B (slot w 1) w=0 then 0#64 else 1#64) ∧
 Outside B (8*sTmp) 8 s.mem t.mem ∧ Keep mmRegs s t := by
 have arrayRoom := Nat.le_trans (slot_le (w:=w) (show 1<8 by decide)) room
 unfold Generate.nonzero
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x8,.x12,.x9] (Q:=fun a =>
  a.gpr .x8=off B (slot w 1) ∧ a.gpr .x12=BitVec.ofNat 64 w ∧ a.gpr .x9=0#64 ∧ a.mem=s.mem)
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sArr 1<32 by decide),hdr_enc (show sW<32 by decide),
    header_read good room (show sArr 1<32 by decide),header_read good room (show sW<32 by decide),
    good.hdr.harr 1 (by decide),good.hdr.hw]
 · rintro a ⟨⟨ptrA,countA,zeroA,memA⟩,restA⟩
   rw [WP.seq_iff]
   refine WP.mono (nonzeroScan_ok (good.scr.congr restA.wr) (by omega) positive size ptrA zeroA countA) ?_
   rintro b ⟨zeroB,memB,restB⟩
   have total := restA.trans restB
   rw [memA] at zeroB
   let flag : Addr := if wv s.mem B (slot w 1) w=0 then 0#64 else 1#64
   refine WP.mono (WP.keep [.x3,.x4,.x9] (Q:=fun t =>t.gpr .x9=flag ∧
    t.mem=b.mem.writeW (off B (8*sTmp)) flag) ?_ rfl rfl rfl) ?_
   · brun [exec_cselc_x,zeroFlag,CondCode.holds,RegUpd.zf_write,
      (total.gpr .x0 (by decide)).trans good.x0,hdr_enc (show sTmp<32 by decide),
      (good.scr.congr total.wr).st (d:=8*sTmp) (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega),
      Bool.toNat_true]
     simp only [show (BitVec.setWidth 64 (0#16))=0#64 from rfl,
      show (BitVec.setWidth 64 (1#16))=1#64 from rfl,BitVec.not_zero]
     have cond : b.gpr .x9+BitVec.allOnes 64+1#64=b.gpr .x9 := by simp [BitVec.add_assoc]
     rw [cond]
     simp only [decide_eq_true_eq,zeroB,flag]
     exact ⟨trivial,trivial⟩
   · rintro t ⟨⟨value,memT⟩,restT⟩
     have frame : Outside B (8*sTmp) 8 s.mem t.mem := by
      rw [memT,memB,memA];exact writeW_outside _ _ _ (by decide)
     have rest : Keep mmRegs s t := (total.trans restT).mono (by simp [mmRegs])
     exact ⟨good_after_header good (by decide) (by decide) frame rest ((rest.gpr .x0 (by simp [mmRegs])).trans good.x0),
      value,by rw [memT,word_writeW_self],frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
