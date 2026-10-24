module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Native strict comparison reuses the verified multiword borrow loop. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem lessHead_ok {s : State} {B : Addr} {Z w a b : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (left : a<8) (right : b<8) :
 WP isa (.block [ldh .x16 (sArr a),ldh .x17 (sArr b),ldh .x14 sW,movi .x7 0,.subs .x .x3 .x7 .x7]) s fun u =>
 (u.gpr .x16=off B (slot w a) ∧ u.gpr .x17=off B (slot w b) ∧ u.gpr .x14=BitVec.ofNat 64 w ∧
  u.gpr .x7=0#64 ∧ u.c=true ∧ u.mem=s.mem) ∧ Keep [.x16,.x17,.x14,.x7,.x3] s u := by
 have hdrA : sArr a<32 := by unfold sArr;omega
 have hdrB : sArr b<32 := by unfold sArr;omega
 refine WP.keep [.x16,.x17,.x14,.x7,.x3] ?_ rfl rfl rfl
 brun [good.x0,hdr_enc hdrA,hdr_enc hdrB,hdr_enc (show sW<32 by decide),
  header_read good room hdrA,header_read good room hdrB,header_read good room (show sW<32 by decide),
  good.hdr.harr a left,good.hdr.harr b right,good.hdr.hw]

theorem less_ok {s : State} {B : Addr} {Z w a b : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (size : w<2^31)
 (left : a<8) (right : b<8) :
 WP isa (Generate.less a b) s fun t =>
 t.gpr .x9=(if wv s.mem B (slot w a) w<wv s.mem B (slot w b) w then 1#64 else 0#64) ∧
 t.mem=s.mem ∧ Keep mmRegs s t := by
 have roomA := Nat.le_trans (slot_le (w:=w) left) room
 have roomB := Nat.le_trans (slot_le (w:=w) right) room
 unfold Generate.less
 rw [WP.seq_iff]
 refine WP.mono (lessHead_ok good room left right) ?_
 · rintro u ⟨⟨ptrA,ptrB,count,zero,carry,memU⟩,restU⟩
   rw [WP.seq_iff]
   refine WP.mono (cmpLoop_ok (good.scr.congr restU.wr) ptrA ptrB count carry (by omega) size (by omega) (by omega)) ?_
   rintro v ⟨carryV,memV,restV⟩
   have total := restU.trans restV
   have zeroV := (restV.gpr .x7 (by decide)).trans zero
   have carry : v.c= !decide (wv s.mem B (slot w a) w<wv s.mem B (slot w b) w) := by rw [memU] at carryV;exact carryV
   refine WP.mono (WP.keep [.x4,.x9] (Q:=fun t =>
    t.gpr .x9=(if wv s.mem B (slot w a) w<wv s.mem B (slot w b) w then 1#64 else 0#64) ∧ t.mem=v.mem)
    ?_ rfl rfl rfl) ?_
   · brun [zeroV,carry]
     split <;> simp_all
   · rintro t ⟨⟨value,memT⟩,restT⟩
     exact ⟨value,(memT.trans memV).trans memU,(total.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
