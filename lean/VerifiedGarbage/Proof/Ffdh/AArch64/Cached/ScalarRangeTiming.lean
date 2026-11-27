module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Source
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Copy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadArray
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
public import VerifiedGarbage.Proof.Ffdh.Domain
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoadTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Ffdh.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! ### `Ffdh.AArch64.Cached.Nonzero`, which only this module used -/

section

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
 · brun [inv.pointer,(scratch.congr inv.keep.wr).ld (d:=e+8*j) (by omega_using [fit, inside])]
 · rintro a ⟨⟨memA,valueA,ptrA⟩,restA⟩
   refine WP.mono (dec_ok a .x12) ?_
   rintro u ⟨⟨count,memU,_⟩,restU⟩
   refine ⟨⟨memU.trans (memA.trans inv.mem),((inv.keep.trans restA).trans restU).mono (by simp),?_,?_⟩,?_⟩
   · rw [restU.gpr .x8 (by decide),ptrA]
     rw [show e+8*j+8=e+8*(j+1) by omega_using []]
   · rw [restU.gpr .x9 (by decide),valueA,BitVec.or_eq_zero_iff,inv.value,inv.mem]
     constructor
     · rintro ⟨low,top⟩ i hi
       rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
       · exact low i hi
       · exact top
     · intro h
       exact ⟨fun i hi =>h i (by omega_using [hi]),h j (by omega_using [])⟩
   · rw [count,restA.gpr .x12 (by decide)]

theorem nonzeroScan_ok {s : State} {B : Addr} {Z e w : Nat}
 (scratch : Scr s B Z) (fit : e+8*w≤Z) (positive : 0<w) (size : w<2^31)
 (pointer : s.gpr .x8=off B e) (zero : s.gpr .x9=0#64) (count : s.gpr .x12=BitVec.ofNat 64 w) :
 WP isa (countLoop .x12 [ld .x3 .x8,.logic .orr .x .x9 .x9 .x3,next .x8]) s fun t =>
 (t.gpr .x9=0#64 ↔ wv s.mem B e w=0) ∧ t.mem=s.mem ∧ Keep [.x3,.x8,.x9,.x12] s t := by
 refine WP.mono (wp_countdown (N:=w) (by omega_using [size]) (by omega_using [positive]) (NonzeroInv s B e)
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
   refine WP.mono (nonzeroScan_ok (good.scr.congr restA.wr) (by omega_using [arrayRoom]) positive size ptrA zeroA countA) ?_
   rintro b ⟨zeroB,memB,restB⟩
   have total := restA.trans restB
   rw [memA] at zeroB
   let flag : Addr := if wv s.mem B (slot w 1) w=0 then 0#64 else 1#64
   refine WP.mono (WP.keep [.x3,.x4,.x9] (Q:=fun t =>t.gpr .x9=flag ∧
    t.mem=b.mem.writeW (off B (8*sTmp)) flag) ?_ rfl rfl rfl) ?_
   · brun [exec_cselc_x,zeroFlag,CondCode.holds,RegUpd.zf_write,
      (total.gpr .x0 (by decide)).trans good.x0,hdr_enc (show sTmp<32 by decide),
      (good.scr.congr total.wr).st (d:=8*sTmp) (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega_using [room, this]),
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

end

end

/-! ### `Ffdh.AArch64.Cached.BoundHead`, which only this module used -/

section

/-! The public domain length selects q or p−1 without inspecting a private scalar. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem boundHead_ok {s : State} {B dom : Addr} {Z w k dl : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (size : k<2^31) (shape : dl=2*k ∨ dl=3*k)
 (pointer : word s.mem B (8*sDom)=dom) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl) :
 WP isa (.block [ldh .x1 sDom,ldh .x2 sLen,ldh .x3 sDL,.lsl .x .x4 .x2 1,.sub .x .x3 .x3 .x4]) s fun t =>
 (t.gpr .x1=dom ∧ t.gpr .x2=BitVec.ofNat 64 k ∧ t.gpr .x3=BitVec.ofNat 64 (dl-2*k) ∧
 t.gpr .x4=BitVec.ofNat 64 (2*k) ∧ t.mem=s.mem) ∧ Keep [.x1,.x2,.x3,.x4] s t := by
 have shift : BitVec.ofNat 64 k <<< 1=BitVec.ofNat 64 (2*k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  omega_using []
 have sub : BitVec.ofNat 64 dl-BitVec.ofNat 64 (2*k)=BitVec.ofNat 64 (dl-2*k) :=
  BitVec.ofNat_sub_ofNat_of_le dl (2*k) (by omega_using [size]) (by omega_using [shape])
 refine WP.keep [.x1,.x2,.x3,.x4] ?_ rfl rfl rfl
 brun [good.x0,hdr_enc (show sDom<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sDL<32 by decide),
  header_read good room (show sDom<32 by decide),header_read good room (show sLen<32 by decide),
  header_read good room (show sDL<32 by decide),pointer,length,domainLength,shift,sub]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.LessTiming`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.Less`, which this module and modules that import it used -/

section

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
 have hdrA : sArr a<32 := by unfold sArr;omega_using [left]
 have hdrB : sArr b<32 := by unfold sArr;omega_using [right]
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
   refine WP.mono (cmpLoop_ok (good.scr.congr restU.wr) ptrA ptrB count carry (by omega_using [positive]) size (by omega_using [roomA]) (by omega_using [roomB])) ?_
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

end

end

/-! Strict comparison has a public limb count and no predicate-dependent trace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem less_ct {a b : Nat} (left : a<8) (right : b<8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
 (check : (taint.check (Taint.ofRegs [.x0])
  (.block [ldh .x16 (sArr a),ldh .x17 (sArr b),ldh .x14 sW,movi .x7 0,.subs .x .x3 .x7 .x7]) hc).isSome=true) :
 RelCT isa (Two GoodW) (Generate.less a b) (fun _ _ => True) := by
 unfold Generate.less
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x16=off q.B (slot q.w a) ∧
  s.gpr .x17=off q.B (slot q.w b) ∧ s.gpr .x14=BitVec.ofNat 64 q.w) [.x0] pins_goodW check ?_)
  (two_taint [.x16,.x17,.x14] ?_ (by taint_decide))
 · rintro q s ⟨mi,good,room⟩
   refine WP.mono (lessHead_ok good room left right) ?_
   rintro t ⟨⟨ptrA,ptrB,count,_,_,_⟩,_⟩
   exact ⟨ptrA,ptrB,count⟩
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.SetLowBit`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.MemoryState`, which the modules that import this one used -/

section

/-! Register-only phases preserve arithmetic state when memory is unchanged. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem good_after_mem {s t : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {rs : List Reg}
 (good : Good s B Z w mi) (mem : t.mem=s.mem) (rest : Keep rs s t) (base : t.gpr .x0=B) : Good t B Z w mi :=
 ⟨good.scr.congr rest.wr,base,mem ▸ good.hdr⟩

theorem ModState.after_mem {p : Parameters} {s t : State} {rs : List Reg}
 (state : ModState p s) (mem : t.mem=s.mem) (rest : Keep rs s t) (base : t.gpr .x0=p.B) : ModState p t :=
 ⟨good_after_mem state.good mem rest base,mem ▸ state.modulus,mem ▸ state.inverse,mem ▸ state.one,mem ▸ state.r2⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The native low-bit update touches exactly one limb of the comparison copy. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/LowOrOne.lean`, which only this module imported.
section

/-! Setting the low bit of a multiword value preserves all its higher bits. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem wv_low_or_one (m : Mem) (B : Addr) {d w : Nat} (positive : 0<w) (fit : d+8*w≤2^64) :
 wv (m.writeW (off B d) (word m B d ||| 1#64)) B d w=2*(wv m B d w/2)+1 := by
 have low := wv_mod64 m B d (by omega_using [positive] : 1≤w)
 have mod2 : (word m B d).toNat%2=wv m B d w%2 := by omega_using [low]
 have split (m : Mem) : wv m B d w=(word m B d).toNat+2^64*wv m B (d+8) (w-1) := by
  have h := wv_add m B d 1 (w-1)
  rw [show 1+(w-1)=w by omega_using [positive]] at h
  simpa only [wv,Nat.mul_zero,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.zero_add,Nat.reduceMul,Nat.reducePow] using h
 have frame := writeW_outside m B (word m B d ||| 1#64) (by omega_using [positive, fit] : d+8≤2^64)
 have orValue := VG.Proof.Ffdh.AArch64.or1_toNat (word m B d)
 change (word m B d ||| 1#64).toNat=(word m B d).toNat+(1-(word m B d).toNat%2) at orValue
 rw [split,word_writeW_self,orValue,
  frame.wv (Or.inr (by omega_using [] : d+8≤d+8)) (by omega_using [positive, fit])]
 have original := split m
 omega_using [original]

end VG.Proof.Ffdh.AArch64.Cached
end

end

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
    good.hdr.harr 1 (by decide),good.scr.ld (d:=slot w 1) (by omega_using [arrayRoom]),good.scr.st (d:=slot w 1) (by omega_using [arrayRoom])]
   rfl
 · rintro t ⟨mem,rest⟩
   have frame : Arrays B w [1] s.mem t.mem := by
    apply Arrays.of_outside (j:=1) (by simp) (o:=slot w 1) (n:=8)
    · rw [mem];exact writeW_outside _ _ _ (by have := good.scr.nowrap;omega_using [arrayRoom, this])
    · omega_using []
    · have := good.scr.nowrap;omega_using []
   refine ⟨good_after_arrays good frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   rw [mem]
   exact wv_low_or_one _ _ positive (by have := good.scr.nowrap;omega_using [arrayRoom, this])

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.NonzeroTiming`, which only this module used -/

section

/-! The zero test's complete trace depends only on public workspace geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem nonzero_ct : RelCT isa (Two GoodW) Generate.nonzero (fun _ _ =>True) := by
 unfold Generate.nonzero
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x0=q.B ∧ s.gpr .x8=off q.B (slot q.w 1) ∧
  s.gpr .x12=BitVec.ofNat 64 q.w) [.x0] pins_goodW (by taint_decide) ?_)
  (two_taint [.x0,.x8,.x12] ?_ (by taint_decide))
 · rintro q s ⟨mi,good,room⟩
   brun [good.x0,hdr_enc (show sArr 1<32 by decide),hdr_enc (show sW<32 by decide),
    header_read good room (show sArr 1<32 by decide),header_read good room (show sW<32 by decide),
    good.hdr.harr 1 (by decide),good.hdr.hw]
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.BoundTiming`, which only this module used -/

section

/-! Choosing q or p−1 and loading the bound exposes no private-scalar data. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

structure BoundPublic where
 workspace : Ws
 ptr : Addr
 k : Nat
 dl : Nat
 positive : 0<workspace.w
 size : workspace.w<2^31
 lengthBound : k<2^31
 shape : dl=2*k ∨ dl=3*k

structure BoundReady (p : BoundPublic) (s : State) : Prop where
 good : GoodW p.workspace s
 pointer : word s.mem p.workspace.B (8*sDom)=p.ptr
 length : word s.mem p.workspace.B (8*sLen)=BitVec.ofNat 64 p.k
 domainLength : word s.mem p.workspace.B (8*sDL)=BitVec.ofNat 64 p.dl

structure BoundHeadReady (p : BoundPublic) (s : State) : Prop where
 good : GoodW p.workspace s
 ptr : s.gpr .x1=p.ptr
 len : s.gpr .x2=BitVec.ofNat 64 p.k
 test : s.gpr .x3=BitVec.ofNat 64 (p.dl-2*p.k)
 offset : s.gpr .x4=BitVec.ofNat 64 (2*p.k)

theorem boundNoQ_ct : RelCT isa (Two fun (p : BoundPublic) s =>GoodW p.workspace s)
 (.seq (copy 5 0) (.block [ldh .x8 (sArr 5),ld .x3 .x8,.subImm .x .x3 .x3 1,st .x3 .x8])) (fun _ _ =>True) := by
 refine RelCT.seq (two_post (Ψ:=fun (p : BoundPublic) s =>GoodW p.workspace s)
  (two_map (fun p =>p.workspace) (fun _ _ h =>h) (copy_ct (by decide : 5<8) (by decide : 0<8) (by taint_decide))) ?_)
  ?_
 · rintro p s ⟨mi,good,room⟩
   refine WP.mono (copy_ok good room p.positive p.size (by decide : 5<8) (by decide : 0<8) (by decide)) ?_
   rintro t ⟨goodT,_,_,_⟩
   exact ⟨mi,goodT,room⟩
 · change RelCT isa (Two fun (p : BoundPublic) s =>GoodW p.workspace s)
    (.block ([ldh .x8 (sArr 5)]++[ld .x3 .x8,.subImm .x .x3 .x3 1,st .x3 .x8])) _
   apply RelCT.block_append
   refine RelCT.seq (two_piece (Ψ:=fun (p : BoundPublic) s =>s.gpr .x8=off p.workspace.B (slot p.workspace.w 5))
    [.x0] (fun p s t hs ht =>pins_goodW _ s t hs ht) (by taint_decide) ?_)
    (two_taint [.x8] (fun p s t hs ht r hr =>by
     have eq : r= .x8 := by simpa using hr
     subst r;exact hs.trans ht.symm) (by taint_decide))
   rintro p s ⟨mi,good,room⟩
   brun [good.x0,hdr_enc (show sArr 5<32 by decide),header_read good room (show sArr 5<32 by decide),good.hdr.harr 5 (by decide)]

theorem scalarBound_ct : RelCT isa (Two BoundReady) Generate.bound (fun _ _ =>True) := by
 unfold Generate.bound
 refine RelCT.seq (two_piece (Ψ:=BoundHeadReady) [.x0]
  (fun _ s t hs ht =>pins_goodW _ s t hs.good ht.good) (by taint_decide) ?_) ?_
 · rintro p s h
   obtain ⟨mi,good,room⟩ := h.good
   refine WP.mono (boundHead_ok good room p.lengthBound p.shape h.pointer h.length h.domainLength) ?_
   rintro t ⟨⟨ptr,len,test,offset,mem⟩,rest⟩
   exact ⟨⟨mi,⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,room⟩,ptr,len,test,offset⟩
 · refine RelCT.ite ?_ ?_ ?_
   · rintro s t ⟨p,hs,ht,_⟩
     rw [eval_zero,eval_zero,hs.test,ht.test]
   · exact boundNoQ_ct.mono (fun _ _ h =>by rcases h.1 with ⟨p,hs,ht,sp⟩;exact ⟨p,hs.good,ht.good,sp⟩) (fun _ _ h =>h)
   · refine (RelCT.seq (two_piece (Ψ:=fun p s =>LoadReady (⟨p.workspace,p.ptr+BitVec.ofNat 64 (2*p.k),p.k⟩ : LoadPublic) s)
      [.x1,.x4] ?_ (by taint_decide) ?_)
      (two_map (fun p =>(⟨p.workspace,p.ptr+BitVec.ofNat 64 (2*p.k),p.k⟩ : LoadPublic)) (fun _ _ h =>h)
       (load_ct (by decide : 5<8) (by taint_decide)))).mono (fun _ _ h =>h.1) (fun _ _ h =>h)
     · intro p s t hs ht r hr
       simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
       rcases hr with rfl|rfl
       · exact hs.ptr.trans ht.ptr.symm
       · exact hs.offset.trans ht.offset.symm
     · rintro p s h
       obtain ⟨mi,good,room⟩ := h.good
       refine WP.mono (WP.keep [.x1] (Q:=fun t =>t.gpr .x1=p.ptr+BitVec.ofNat 64 (2*p.k) ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
       · brun [h.ptr,h.offset]
       · rintro t ⟨⟨ptr,mem⟩,rest⟩
         exact ⟨⟨mi,⟨good.scr.congr rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,mem ▸ good.hdr⟩,room⟩,
          ptr,(rest.gpr .x2 (by decide)).trans h.len⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.SourceEncoding`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.RangeFrame`, which the modules that import this one used -/

section

/-! ### `Ffdh.AArch64.Cached.ScalarRange`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.ScalarBound`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.BoundNoQ`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.LowDecrement`, which only this module used -/

section

/-! An odd modulus permits p−1 by decrementing only its low limb, without a borrow. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.Proof.Bignum

theorem wv_low_decrement (m : Mem) (B : Addr) {d w : Nat} (positive : 0<w)
 (fit : d+8*w≤2^64) (odd : wv m B d w%2=1) :
 wv (m.writeW (off B d) (word m B d-1#64)) B d w=wv m B d w-1 := by
 obtain low := wv_mod64 m B d (by omega_using [positive] : 1≤w)
 obtain positiveLow : 0<(word m B d).toNat := by
  have : wv m B d w%2^64%2=1 := by omega_using [odd]
  rw [low] at this
  omega_using [this]
 obtain sub : (word m B d-1#64).toNat=(word m B d).toNat-1 := by
  simp only [BitVec.toNat_sub,show (1#64).toNat=1 from rfl]
  have := (word m B d).isLt
  omega_using [positiveLow]
 have split (m : Mem) : wv m B d w= (word m B d).toNat + 2^64*wv m B (d+8) (w-1) := by
  obtain h := wv_add m B d 1 (w-1)
  rw [show 1+(w-1)=w by omega_using [positive]] at h
  simpa only [wv,Nat.mul_zero,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.zero_add,Nat.reduceMul,Nat.reducePow] using h
 obtain frame := writeW_outside m B (word m B d-1#64) (by omega_using [positive, fit] : d+8≤2^64)
 rw [split,word_writeW_self,sub,frame.wv (Or.inr (by omega_using [] : d+8≤d+8)) (by omega_using [positive, fit]),split]
 omega_using [positiveLow]

end VG.Proof.Ffdh.AArch64.Cached

end

end


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
 obtain arrayRoom := Nat.le_trans (slot_le (w:=w) (show 5<8 by decide)) room
 refine WP.mono (WP.keep [.x8,.x3] (Q:=fun t =>t.mem=a.mem.writeW (off B (slot w 5)) (word a.mem B (slot w 5)-1#64)) ?_ rfl rfl rfl) ?_
 · brun [goodA.x0,hdr_enc (show sArr 5<32 by decide),header_read goodA room (show sArr 5<32 by decide),
    goodA.hdr.harr 5 (by decide),goodA.scr.ld (d:=slot w 5) (by omega_using [arrayRoom]),goodA.scr.st (d:=slot w 5) (by omega_using [arrayRoom])]
 · rintro t ⟨memT,restT⟩
   obtain nowrap : slot w 5+8*w≤2^64 := by have := goodA.scr.nowrap;omega_using [arrayRoom, this]
   obtain value : wv t.mem B (slot w 5) w=wv s.mem B (slot w 0) w-1 := by
    rw [memT,wv_low_decrement _ _ positive nowrap (by rw [valueA];exact odd),valueA]
   obtain frameT : Arrays B w [5] a.mem t.mem := by
    apply Arrays.of_outside (j:=5) (by simp) (o:=slot w 5) (n:=8)
    · rw [memT];exact writeW_outside _ _ _ (by omega_using [positive, nowrap])
    · omega_using []
    · omega_using []
   obtain rest : Keep mmRegs s t := (restA.trans restT).mono (by simp [mmRegs])
   exact ⟨good_after_arrays goodA frameT restT ((restT.gpr .x0 (by decide)).trans goodA.x0),
    value,frameA.trans frameT,rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The rejection bound is exactly the reviewed q-or-p−1 value for both domain encodings. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem scalarBound_ok {s : State} {B ptr : Addr} {Z w k dl : Nat} {mi : BitVec 64} {dom : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (words : w=(k+7)/8) (positive : 0<k) (size : k<2^31)
 (shape : dl=2*k ∨ dl=3*k) (domLength : dom.length=dl) (source : Src s B Z ptr dom)
 (pointer : word s.mem B (8*sDom)=ptr) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (modulus : wv s.mem B (slot w 0) w=(Spec.Ffdh.domainOf k dom).p)
 (odd : (Spec.Ffdh.domainOf k dom).p%2=1) :
 WP isa Generate.bound s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 5) w=Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ∧
 Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Generate.bound
 rw [WP.seq_iff]
 refine WP.mono (boundHead_ok good room size shape pointer length domainLength) ?_
 rintro a ⟨⟨ptrA,lenA,testA,offsetA,memA⟩,restA⟩
 obtain goodA : Good a B Z w mi :=
  ⟨good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans good.x0,memA ▸ good.hdr⟩
 obtain sourceA := source.congrK (fun x _ =>by rw [memA]) restA
 by_cases noQ : dl=2*k
 · have branch := boundNoQ_ok goodA room (by rw [words];omega_using [positive]) (by rw [words];omega_using [size])
    (by rw [memA,modulus];exact odd)
   obtain condition : isa.eval (.zero .x .x3) a=some true := by rw [eval_zero,testA,noQ,Nat.sub_self];decide
   obtain ⟨tr,t,run,goodT,value,frame,rest⟩ := branch
   refine ⟨_,t,.iteT condition run,goodT,?_,?_,(restA.trans rest).mono (by simp [mmRegs])⟩
   · rw [memA,modulus] at value
     simpa only [Spec.Ffdh.scalarBound,Spec.Ffdh.domainOf,
      ite_eq_right (by omega_using [positive, domLength, noQ] : ¬dom.length=3*k),Option.getD_none] using value
   · rw [←memA];exact frame
 · have three : dl=3*k := by omega_using [shape, noQ]
   obtain condition : isa.eval (.zero .x .x3) a=some false := by
    rw [eval_zero,testA,three]
    obtain nonzero : BitVec.ofNat 64 (3*k-2*k)≠0#64 := by
     intro eq;have := congrArg BitVec.toNat eq;change (3*k-2*k)%2^64=0 at this;omega_using [room, words, positive, size, shape, domLength, pointer, length, domainLength, modulus, odd, ptrA, lenA, testA, offsetA, noQ, three, eq, this]
    simp [nonzero]
   obtain body : WP isa (.seq (.block [.add .x .x1 .x1 .x4]) (load 5)) a fun t =>
    Good t B Z w mi ∧ wv t.mem B (slot w 5) w=Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ∧
    Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
    rw [WP.seq_iff]
    refine WP.mono (WP.keep [.x1] (Q:=fun b =>b.gpr .x1=ptr+BitVec.ofNat 64 (2*k) ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
    · brun [ptrA,offsetA]
    · rintro b ⟨⟨ptrB,memB⟩,restB⟩
      obtain goodB : Good b B Z w mi :=
       ⟨goodA.scr.congr restB.wr,(restB.gpr .x0 (by decide)).trans goodA.x0,memB ▸ goodA.hdr⟩
      obtain srcB := sourceA.congrK (fun x _ =>by rw [memB]) restB
      refine WP.mono (loadArray_ok goodB room words positive size (by decide : 5<8)
       (src_take (src_drop srcB (2*k)) k) (by simp only [List.length_take,List.length_drop];omega_using [shape, domLength, noQ])
       ptrB ((restB.gpr .x2 (by decide)).trans lenA)) ?_
      rintro t ⟨goodT,value,frame,restT⟩
      refine ⟨goodT,?_,?_,((restA.trans restB).trans restT).mono (by simp [mmRegs])⟩
      · simpa only [Spec.Ffdh.scalarBound,Spec.Ffdh.domainOf,ite_eq_left (by omega_using [shape, domLength, noQ] : dom.length=3*k),Option.getD_some] using value
      · rw [←memA,←memB];exact frame
   obtain ⟨tr,t,run,post⟩ := body
   exact ⟨_,t,.iteF condition run,post⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The complete rejection predicate is 0<x<q, or 0<x<p−1, at a fixed public width. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def scalarRanges (w : Nat) : List (Nat × Nat) :=
 [(slot w 1,8*(w+2)),(slot w 5,8*(w+2)),(8*sTmp,8)]

theorem scalarRange_ok {s : State} {B xp dp : Addr} {Z w k dl : Nat} {mi : BitVec 64} {dom bs : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (words : w=(k+7)/8) (positive : 0<k) (size : k<2^31)
 (shape : dl=2*k ∨ dl=3*k) (domLength : dom.length=dl)
 (domainSource : Src s B Z dp dom) (scalarSource : Src s B Z xp bs) (bsLength : bs.length=k)
 (output : word s.mem B (8*sX)=xp) (domain : word s.mem B (8*sDom)=dp)
 (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k) (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (modulus : wv s.mem B (slot w 0) w=(Spec.Ffdh.domainOf k dom).p)
 (odd : (Spec.Ffdh.domainOf k dom).p%2=1) :
 WP isa Generate.scalarRange s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 1) w=Spec.Rsa.os2ip bs ∧
 t.gpr .x9=(if 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) ∧
 Frm B (scalarRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
 obtain wPositive : 0<w := by rw [words];omega_using [positive]
 obtain wSize : w<2^31 := by rw [words];omega_using [size]
 obtain nowrap : slot w 8≤2^64 := by have := good.scr.nowrap;omega_using [room, this]
 obtain array0 := slot_le (w:=w) (show 0<8 by decide)
 obtain array1 := slot_le (w:=w) (show 1<8 by decide)
 unfold Generate.scalarRange
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2] (Q:=fun a =>a.gpr .x1=xp ∧ a.gpr .x2=BitVec.ofNat 64 k ∧ a.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),
    header_read good room (show sX<32 by decide),header_read good room (show sLen<32 by decide),output,length]
 · rintro a ⟨⟨ptrA,lenA,memA⟩,restA⟩
   obtain goodA : Good a B Z w mi := ⟨good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans good.x0,memA ▸ good.hdr⟩
   obtain scalarA := scalarSource.congrK (fun x _ =>by rw [memA]) restA
   rw [WP.seq_iff]
   refine WP.mono (loadArray_ok goodA room words positive size (by decide : 1<8) scalarA bsLength ptrA lenA) ?_
   rintro b ⟨goodB,valueB,frameB,restB⟩
   rw [WP.seq_iff]
   refine WP.mono (nonzero_ok goodB room wPositive wSize) ?_
   rintro c ⟨goodC,_,nonzeroC,frameC,restC⟩
   obtain before := (restA.trans restB).trans restC
   obtain inscrB := InScr.of_arrays frameB room (by simp : ∀ i∈[1],i<8)
   obtain inscrC : InScr B Z b.mem c.mem := InScr.of_outside frameC (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega_using [room, this])
   obtain inscrSA : InScr B Z s.mem a.mem := by intro x hx;rw [memA]
   obtain sourceC := domainSource.congrK ((inscrSA.trans inscrB).trans inscrC) before
   have headerC (i : Nat) (hi : i<32) (different : i≠sTmp) : word c.mem B (8*i)=word s.mem B (8*i) := by
    rw [header_other frameC (by decide) hi different,arrays_header frameB hi,memA]
   obtain modulusC : wv c.mem B (slot w 0) w=(Spec.Ffdh.domainOf k dom).p := by
    rw [frameC.wv (Or.inr (hdr_lt_slot w 0 (show sTmp<32 by decide))) (by omega_using [nowrap, array0]),
     frameB.wv_of_not_mem (by decide) (by decide) (by have := good.scr.nowrap;omega_using [room, this]),memA]
    exact modulus
   obtain valueC : wv c.mem B (slot w 1) w=Spec.Rsa.os2ip bs := by
    rw [frameC.wv (Or.inr (hdr_lt_slot w 1 (show sTmp<32 by decide))) (by omega_using [nowrap, array1])];exact valueB
   rw [WP.seq_iff]
   refine WP.mono (scalarBound_ok goodC room words positive size shape domLength sourceC
    ((headerC sDom (by decide) (by decide)).trans domain)
    ((headerC sLen (by decide) (by decide)).trans length)
    ((headerC sDL (by decide) (by decide)).trans domainLength) modulusC odd) ?_
   rintro d ⟨goodD,boundD,frameD,restD⟩
   obtain valueD : wv d.mem B (slot w 1) w=Spec.Rsa.os2ip bs :=
    (frameD.wv_of_not_mem (by decide) (by decide) (by have := good.scr.nowrap;omega_using [room, this])).trans valueC
   obtain nzD : word d.mem B (8*sTmp)=(if Spec.Rsa.os2ip bs=0 then 0#64 else 1#64) := by
    rw [arrays_header frameD (by decide),nonzeroC,valueB]
   rw [WP.seq_iff]
   refine WP.mono (less_ok goodD room wPositive wSize (by decide : 1<8) (by decide : 5<8)) ?_
   rintro e ⟨lessE,memE,restE⟩
   rw [valueD,boundD] at lessE
   obtain rest := ((before.trans restD).trans restE)
   obtain maskE : word e.mem B (8*sTmp)=(if Spec.Rsa.os2ip bs=0 then 0#64 else 1#64) := by rw [memE];exact nzD
   obtain flag : (if Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) &&&
    (if Spec.Rsa.os2ip bs=0 then 0#64 else 1#64)=
    (if 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) := by
    split <;> split <;> rename_i h₁ h₂ <;> simp [h₁, h₂]
   refine WP.mono (WP.keep [.x3,.x9] (Q:=fun t =>
    t.gpr .x9=(if 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) ∧ t.mem=e.mem)
    ?_ rfl rfl rfl) ?_
   · brun [(rest.gpr .x0 (by simp [mmRegs])).trans good.x0,hdr_enc (show sTmp<32 by decide),
      (good.scr.congr rest.wr).ld (d:=8*sTmp) (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega_using [room, this]),maskE,lessE,flag]
   · rintro t ⟨⟨flagT,memT⟩,restT⟩
     obtain total : Keep mmRegs s t := (rest.trans restT).mono (by decide)
     obtain same : t.mem=d.mem := memT.trans memE
     obtain goodT : Good t B Z w mi :=
      ⟨good.scr.congr total.wr,(total.gpr .x0 (by simp [mmRegs])).trans good.x0,same ▸ goodD.hdr⟩
     obtain first : Frm B (scalarRanges w) s.mem b.mem := by
      rw [←memA];exact Frm.of_arrays frameB (by simp [scalarRanges])
     obtain second : Frm B (scalarRanges w) b.mem c.mem := Frm.of_outside frameC (by simp [scalarRanges])
     obtain third : Frm B (scalarRanges w) c.mem d.mem := Frm.of_arrays frameD (by simp [scalarRanges])
     exact ⟨goodT,by rw [same];exact valueD,flagT,by rw [same];exact (first.trans second).trans third,total⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PublicRange`, which only this module used -/

section

/-! Public powers are checked for 1<y<p−1 without repeating their proven subgroup test. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def publicRangeRanges (w : Nat) : List (Nat × Nat) := [(slot w 1,8*(w+2)),(8*sTmp,8)]

theorem publicRange_ok {p : Parameters} {s : State} (state : ModState p s) (odd : p.P%2=1) :
 WP isa Generate.publicRange s fun t =>
 ModState p t ∧ wv t.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w ∧
 t.gpr .x9=(if 1<wv s.mem p.B (slot p.w 6) p.w ∧ wv s.mem p.B (slot p.w 6) p.w<p.P-1 then 1#64 else 0#64) ∧
 word t.mem p.B (8*sTmp)=t.gpr .x9 ∧ Frm p.B (publicRangeRanges p.w) s.mem t.mem ∧ Keep mmRegs s t := by
 obtain positive : 0<p.w := by have := p.positive;omega_using [this]
 obtain nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := state.good.scr.nowrap;have := p.room;omega_arith
 obtain yRoom := slot_le (w:=p.w) (show 6<8 by decide)
 unfold Generate.publicRange
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (less_ok state.good p.room positive p.width (by decide : 7<8) (by decide : 6<8)) ?_
 rintro a ⟨valueA,memA,restA⟩
 rw [state.one] at valueA
 obtain stateA := state.after_mem memA restA ((restA.gpr .x0 (by simp [mmRegs])).trans state.good.x0)
 rw [WP.seq_iff]
 refine WP.mono (store_control_ok stateA.good p.room (by decide : 16≤sTmp) (by decide : sTmp<32) .x9) ?_
 rintro b ⟨goodB,memB,frameB,restB⟩
 obtain stateB := stateA.after_header goodB frameB (by decide : sTmp<32)
 obtain flagB : word b.mem p.B (8*sTmp)=(if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64) := by
  rw [memB,word_writeW_self];exact valueA
 obtain yB : wv b.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w := by
  rw [frameB.wv (Or.inr (hdr_lt_slot p.w 6 (show sTmp<32 by decide))) (by omega_using [nowrap, yRoom]),memA]
 rw [WP.seq_iff]
 refine WP.mono (copy_ok goodB p.room positive p.width (by decide : 1<8) (by decide : 6<8) (by decide)) ?_
 rintro c ⟨goodC,valueC,frameC,restC⟩
 obtain stateC := stateB.after_arrays goodC frameC (by decide) (by decide) (by decide)
 rw [WP.seq_iff]
 refine WP.mono (setLowBit_ok goodC p.room positive) ?_
 rintro d ⟨goodD,valueD,frameD,restD⟩
 obtain stateD := stateC.after_arrays goodD frameD (by decide) (by decide) (by decide)
 obtain valueD : wv d.mem p.B (slot p.w 1) p.w=2*(wv s.mem p.B (slot p.w 6) p.w/2)+1 := by rw [valueD,valueC,yB]
 obtain yD : wv d.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w :=
  (frameD.wv_of_not_mem (by decide) (by decide) nowrap).trans
   ((frameC.wv_of_not_mem (by decide) (by decide) nowrap).trans yB)
 obtain flagD : word d.mem p.B (8*sTmp)=(if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64) := by
  rw [arrays_header frameD (by decide),arrays_header frameC (by decide)];exact flagB
 rw [WP.seq_iff]
 refine WP.mono (less_ok goodD p.room positive p.width (by decide : 1<8) (by decide : 0<8)) ?_
 rintro e ⟨valueE,memE,restE⟩
 rw [valueD,stateD.modulus] at valueE
 simp only [VG.Proof.Ffdh.lt_pm1 odd] at valueE
 obtain total := (((restA.trans restB).trans restC).trans restD).trans restE
 obtain goodE := good_after_mem goodD memE restE ((restE.gpr .x0 (by simp [mmRegs])).trans goodD.x0)
 obtain flagE : word e.mem p.B (8*sTmp)=(if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64) := by rw [memE];exact flagD
 let flag : Addr := if 1<wv s.mem p.B (slot p.w 6) p.w ∧ wv s.mem p.B (slot p.w 6) p.w<p.P-1 then 1#64 else 0#64
 obtain combine : (if wv s.mem p.B (slot p.w 6) p.w<p.P-1 then 1#64 else 0#64) &&&
  (if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64)=flag := by
  unfold flag
  split <;> split <;> simp_all
 refine WP.mono (WP.keep [.x3,.x9] (Q:=fun t =>t.gpr .x9=flag ∧ t.mem=e.mem.writeW (off p.B (8*sTmp)) flag) ?_ rfl rfl rfl) ?_
 · brun [goodE.x0,hdr_enc (show sTmp<32 by decide),header_read goodE p.room (show sTmp<32 by decide),
    goodE.scr.st (d:=8*sTmp) (by have := hdr_lt_slot p.w 8 (show sTmp<32 by decide);have := p.room;omega_arith),
    flagE,valueE,combine]
 · rintro t ⟨⟨flagT,memT⟩,restT⟩
   obtain frameT : Outside p.B (8*sTmp) 8 e.mem t.mem := by rw [memT];exact writeW_outside _ _ _ (by decide)
   obtain stateE := stateD.after_mem memE restE goodE.x0
   obtain goodT := good_after_header goodE (by decide) (by decide) frameT restT ((restT.gpr .x0 (by decide)).trans goodE.x0)
   obtain stateT := stateE.after_header goodT frameT (by decide)
   obtain yT : wv t.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w := by
    rw [frameT.wv (Or.inr (hdr_lt_slot p.w 6 (show sTmp<32 by decide))) (by omega_using [nowrap, yRoom]),memE];exact yD
   obtain first : Frm p.B (publicRangeRanges p.w) s.mem b.mem := by
    rw [←memA];exact Frm.of_outside frameB (by simp [publicRangeRanges])
   obtain middle : Frm p.B (publicRangeRanges p.w) b.mem d.mem :=
    (Frm.of_arrays frameC (by simp [publicRangeRanges])).trans (Frm.of_arrays frameD (by simp [publicRangeRanges]))
   obtain last : Frm p.B (publicRangeRanges p.w) d.mem t.mem := by
    rw [←memE];exact Frm.of_outside frameT (by simp [publicRangeRanges])
   exact ⟨stateT,yT,flagT,by rw [memT,word_writeW_self,flagT],(first.trans middle).trans last,
    (total.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! Range checks preserve the canonical field, scalar bytes and comb controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem scalarRanges_le (w : Nat) : ∀ r∈scalarRanges w,r.1+r.2≤slot w 8 := by
 simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp];omega_using []

theorem publicRangeRanges_le (w : Nat) : ∀ r∈publicRangeRanges w,r.1+r.2≤slot w 8 := by
 simp only [publicRangeRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp];omega_using []

theorem scalarFrame_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (scalarRanges w) m m') (inside : i<32) (different : i≠sTmp) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq _ (by omega_using [inside])
 simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp] at *;omega_arith

theorem publicRangeFrame_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (publicRangeRanges w) m m') (inside : i<32) (different : i≠sTmp) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq _ (by omega_using [inside])
 simp only [publicRangeRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp] at *;omega_arith

theorem FieldInitial.after_scalarRange {p : Parameters} {s t : State}
 (field : FieldInitial p s) (good : Good t p.B p.Z p.w p.mi) (frame : Frm p.B (scalarRanges p.w) s.mem t.mem) : FieldInitial p t := by
 obtain nowrap : slot p.w 8≤2^64 := by have := field.good.scr.nowrap;have := p.room;omega_arith
 have same (j : Nat) (allowed : j=0 ∨ j=4) : wv t.mem p.B (slot p.w j) p.w=wv s.mem p.B (slot p.w j) p.w := by
  apply frame.wv_eq
  · simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
    rintro _ (rfl|rfl|rfl)
    all_goals rcases allowed with rfl|rfl <;> dsimp only [slot,hdrBytes,sTmp] <;>omega_using []
  · rcases allowed with rfl|rfl <;> dsimp only [slot,hdrBytes] at * <;>omega_using [nowrap]
 obtain wordSame : word t.mem p.B (slot p.w 0)=word s.mem p.B (slot p.w 0) := by
  apply frame.word_eq
  · simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
    rintro _ (rfl|rfl|rfl)
    all_goals have := p.positive;dsimp only [slot,hdrBytes,sTmp];omega_using []
  · have := p.positive;dsimp only [slot,hdrBytes] at *;omega_using []
 refine ⟨good,(same 0 (by simp)).trans field.modulus,?_,(same 4 (by simp)).trans field.r2⟩
 rw [wordSame]
 exact field.inverse

theorem Controls.after_scalarRange {B src ctx : Addr} {k N w : Nat} {m : State} {t : State}
 (h : Controls B src ctx k N m) (frame : Frm B (scalarRanges w) m.mem t.mem) : Controls B src ctx k N t :=
 ⟨(scalarFrame_header frame (by decide) (by decide)).trans h.context,
  (scalarFrame_header frame (by decide) (by decide)).trans h.source,
  (scalarFrame_header frame (by decide) (by decide)).trans h.length,
  (scalarFrame_header frame (by decide) (by decide)).trans h.bits,
  (scalarFrame_header frame (by decide) (by decide)).trans h.rows⟩

theorem Initial.after_scalarRange {p : Parameters} {s t : State} {bs : List Byte} {rs : List Reg}
 (h : Initial p bs s) (good : Good t p.B p.Z p.w p.mi) (frame : Frm p.B (scalarRanges p.w) s.mem t.mem)
 (rest : Keep rs s t) : Initial p bs t :=
 ⟨h.toFieldInitial.after_scalarRange good frame,h.controls.after_scalarRange frame,
  h.reads.after_inscr (InScr.of_frm frame (fun r hr =>Nat.le_trans (scalarRanges_le _ r hr) p.room)) rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Byte views are exact fixed-length encodings, including leading zero padding. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem source_bytesAt {ptr : Addr} {bs : List Byte} {s : State} (source : Source ptr bs s) :
 Spec.Rsa.bytesAt s.mem ptr bs.length=bs := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
 · intro i hi hj
   simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
   have value := source.bytes i hj
   simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using value

theorem source_of_bytesAt (s : State) (ptr : Addr) (k : Nat)
 (readable : ∀ i<k,InRegions (s.rd++s.wr) (ptr+BitVec.ofNat 64 i) 1) :
 Source ptr (Spec.Rsa.bytesAt s.mem ptr k) s := by
 constructor
 · intro i hi
   exact readable i (by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi)
 · intro i hi
   have inside : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
   simp only [Spec.Rsa.bytesAt,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range inside,Option.map_some,Option.getD_some]

theorem source_encoding {ptr : Addr} {bs : List Byte} {s : State} (source : Source ptr bs s) :
 Spec.Rsa.bytesAt s.mem ptr bs.length=Spec.Rsa.i2osp (Spec.Rsa.os2ip bs) bs.length := by
 rw [source_bytesAt source,VG.Proof.Rsa.i2osp_os2ip]

theorem source_src {ptr B : Addr} {Z : Nat} {bs : List Byte} {s : State}
 (source : Source ptr bs s) (outside : ∀ i<bs.length,Z≤ofs B (ptr+BitVec.ofNat 64 i)) : Src s B Z ptr bs := by
 refine ⟨source.readable,?_,outside⟩
 intro i hi
 simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using source.bytes i hi

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.ScalarTimingState`, which only this module used -/

section

/-! The rejection checks preserve all public controls and immutable scalar/context inputs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure ScalarPublic where
 p : Parameters
 dp : Addr
 dl : Nat
 dom : List Byte
 words : p.w=(p.k+7)/8
 positive : 0<p.k
 size : p.k<2^31
 shape : dl=2*p.k ∨ dl=3*p.k
 domLength : dom.length=dl
 modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p
 odd : p.P%2=1

structure ScalarState (q : ScalarPublic) (bs : List Byte) (s : State) : Prop where
 initial : Initial q.p bs s
 length : bs.length=q.p.k
 source : Src s q.p.B q.p.Z q.dp q.dom
 domain : word s.mem q.p.B (8*sDom)=q.dp
 domainLength : word s.mem q.p.B (8*sDL)=BitVec.ofNat 64 q.dl

def ScalarReady (q : ScalarPublic) (s : State) : Prop := ∃ bs,ScalarState q bs s

theorem ScalarState.after {q : ScalarPublic} {bs : List Byte} {s t : State} {rs : List Reg}
 (h : ScalarState q bs s) (good : Good t q.p.B q.p.Z q.p.w q.p.mi)
 (frame : Frm q.p.B (scalarRanges q.p.w) s.mem t.mem) (rest : Keep rs s t) : ScalarState q bs t :=
 ⟨h.initial.after_scalarRange good frame rest,h.length,
  h.source.congrK (InScr.of_frm frame (fun r hr =>Nat.le_trans (scalarRanges_le _ r hr) q.p.room)) rest,
  (scalarFrame_header frame (by decide) (by decide)).trans h.domain,
  (scalarFrame_header frame (by decide) (by decide)).trans h.domainLength⟩

theorem ScalarState.after_mem {q : ScalarPublic} {bs : List Byte} {s t : State} {rs : List Reg}
 (h : ScalarState q bs s) (mem : t.mem=s.mem) (rest : Keep rs s t) (base : t.gpr .x0=q.p.B) : ScalarState q bs t :=
 h.after (good_after_mem h.initial.good mem rest base) (fun a _ =>by rw [mem]) rest

def scalarWs (q : ScalarPublic) : Ws := ⟨q.p.B,q.p.Z,q.p.w⟩

def scalarBoundPublic (q : ScalarPublic) : BoundPublic :=
 ⟨scalarWs q,q.dp,q.p.k,q.dl,by change 0<q.p.w;have :=q.p.positive;omega_using [this],q.p.width,q.size,q.shape⟩

theorem scalarReady_bound {q : ScalarPublic} {s : State} (h : ScalarReady q s) : BoundReady (scalarBoundPublic q) s := by
 obtain ⟨bs,h⟩ :=h
 exact ⟨⟨q.p.mi,h.initial.good,q.p.room⟩,h.domain,(by change word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k;rw [←h.length];exact h.initial.controls.length),h.domainLength⟩

theorem scalarReady_nonzero {q : ScalarPublic} {s : State} (h : ScalarReady q s) :
 WP isa Generate.nonzero s (ScalarReady q) := by
 obtain ⟨bs,h⟩ :=h
 refine WP.mono (nonzero_ok h.initial.good q.p.room (by have :=q.p.positive;omega_using [this]) q.p.width) ?_
 rintro t ⟨good,_,_,frame,rest⟩
 exact ⟨bs,h.after good (Frm.of_outside frame (by simp [scalarRanges])) rest⟩

theorem scalarReady_bound_ok {q : ScalarPublic} {s : State} (h : ScalarReady q s) :
 WP isa Generate.bound s (ScalarReady q) := by
 obtain ⟨bs,h⟩ :=h
 refine WP.mono (scalarBound_ok h.initial.good q.p.room q.words q.positive q.size q.shape q.domLength h.source
  h.domain (h.length ▸ h.initial.controls.length) h.domainLength (h.initial.modulus.trans q.modulus)
  (by rw [←q.modulus];exact q.odd)) ?_
 rintro t ⟨good,_,frame,rest⟩
 exact ⟨bs,h.after good (Frm.of_arrays frame (by simp [scalarRanges])) rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The complete scalar rejection predicate scans a fixed public geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def ScalarLoadReady (q : ScalarPublic) (s : State) : Prop :=
 ScalarReady q s ∧ s.gpr .x1=q.p.src ∧ s.gpr .x2=BitVec.ofNat 64 q.p.k

theorem scalarRange_ct : RelCT isa (Two ScalarReady) Generate.scalarRange (fun _ _ =>True) := by
 unfold Generate.scalarRange
 simp only [seqs]
 refine RelCT.seq (two_piece (Ψ:=ScalarLoadReady) [.x0] ?_ (by taint_decide) ?_) ?_
 · rintro q s t ⟨bs,hs⟩ ⟨bt,ht⟩ r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.initial.good.x0.trans ht.initial.good.x0.symm
 · rintro q s ⟨bs,h⟩
   have good := h.initial.good
   have x := h.initial.controls.source
   have len := h.initial.controls.length
   rw [h.length] at len
   refine WP.mono (WP.keep [.x1,.x2] (Q:=fun t =>
    t.gpr .x1=q.p.src ∧ t.gpr .x2=BitVec.ofNat 64 q.p.k ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [good.x0,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),
      header_read good q.p.room (show sX<32 by decide),header_read good q.p.room (show sLen<32 by decide),x,len]
   · rintro t ⟨⟨ptr,len,mem⟩,rest⟩
     exact ⟨⟨bs,h.after_mem mem rest ((rest.gpr .x0 (by decide)).trans good.x0)⟩,ptr,len⟩
 · refine RelCT.seq (two_post (Ψ:=ScalarReady)
    (two_map (fun q =>(⟨scalarWs q,q.p.src,q.p.k⟩ : LoadPublic))
     (fun q s h =>by obtain ⟨⟨bs,h⟩,ptr,len⟩:=h;exact ⟨⟨q.p.mi,h.initial.good,q.p.room⟩,ptr,len⟩)
     (load_ct (by decide : 1<8) (by taint_decide))) ?_) ?_
   · rintro q s ⟨⟨bs,h⟩,ptr,len⟩
     refine WP.mono (loadArray_ok h.initial.good q.p.room q.words q.positive q.size (by decide : 1<8)
      (source_src h.initial.reads.source h.initial.reads.scalarOutside) h.length ptr len) ?_
     rintro t ⟨good,_,frame,rest⟩
     exact ⟨bs,h.after good (Frm.of_arrays frame (by simp [scalarRanges])) rest⟩
   · refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarWs (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨q.p.mi,h.initial.good,q.p.room⟩) nonzero_ct)
      (fun _ _ h =>scalarReady_nonzero h)) ?_
     refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarBoundPublic (fun _ _ h =>scalarReady_bound h) scalarBound_ct)
      (fun _ _ h =>scalarReady_bound_ok h)) ?_
     refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarWs (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨q.p.mi,h.initial.good,q.p.room⟩)
       (less_ct (by decide : 1<8) (by decide : 5<8) (by taint_decide))) ?_)
      (two_taint [.x0] ?_ (by taint_decide))
     · rintro q s ⟨bs,h⟩
       refine WP.mono (less_ok h.initial.good q.p.room (by have :=q.p.positive;omega_using [this]) q.p.width
        (by decide : 1<8) (by decide : 5<8)) ?_
       rintro t ⟨_,mem,rest⟩
       exact ⟨bs,h.after_mem mem rest ((rest.gpr .x0 (by simp [mmRegs])).trans h.initial.good.x0)⟩
     · rintro q s t ⟨bs,hs⟩ ⟨bt,ht⟩ r hr
       have eq : r= .x0 := by simpa using hr
       subst r
       exact hs.initial.good.x0.trans ht.initial.good.x0.symm

end VG.Proof.Ffdh.AArch64.Cached
