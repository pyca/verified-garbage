module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Stable
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Controls
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ffdh.AArch64.Cached.Digit`, which only this module used -/

section

/-! Public header controls drive the proved five-tooth scalar gather. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem digitArgs_ok {s : State} {B src ctx : Addr} {Z w N i : Nat} {mi : BitVec 64} {bs : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (controls : Controls B src ctx bs.length N s)
 (counter : Counter B (i+1) s) (indexFit : i+1<2^64) :
 WP isa (.block [ldh .x1 sX,ldh .x2 sLen,ldh .x9 sI,.subImm .x .x9 .x9 1,
 ldh .x4 sRows,ldh .x5 sBits,movi .x16 0]) s fun t =>
 (t.gpr .x1=src ∧ t.gpr .x2=BitVec.ofNat 64 bs.length ∧ t.gpr .x9=BitVec.ofNat 64 i ∧
 t.gpr .x4=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N) ∧ t.gpr .x5=BitVec.ofNat 64 N ∧
 t.gpr .x16=0#64 ∧ t.mem=s.mem) ∧ Keep [.x1,.x2,.x4,.x5,.x9,.x16] s t := by
 refine WP.keep [.x1,.x2,.x4,.x5,.x9,.x16] ?_ rfl rfl rfl
 have decrement : BitVec.ofNat 64 (i+1)-1#64=BitVec.ofNat 64 i := by
  rw [BitVec.ofNat_sub_ofNat_of_le (i+1) 1 (by decide) (by omega)]
  congr 1
 unfold Counter at counter
 brun [good.x0,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),
 hdr_enc (show sI<32 by decide),hdr_enc (show sRows<32 by decide),hdr_enc (show sBits<32 by decide),
 header_read good room (show sX<32 by decide),header_read good room (show sLen<32 by decide),
 header_read good room (show sI<32 by decide),header_read good room (show sRows<32 by decide),
 header_read good room (show sBits<32 by decide),
 controls.source,controls.length,controls.rows,controls.bits,counter,decrement]

theorem digit_ok {s : State} {B src ctx : Addr} {Z w N i : Nat} {mi : BitVec 64} {bs : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (controls : Controls B src ctx bs.length N s)
 (counter : Counter B (i+1) s) (source : Source src bs s)
 (size : bs.length<2^31) (widthBound : N≤8*bs.length)
 (positions : i+5*Spec.Rsa.FixedBaseComb.rows N<2^63) (bound : Spec.Rsa.os2ip bs<2^N) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.digit s fun t =>
 Good t B Z w mi ∧ Controls B src ctx bs.length N t ∧ Counter B (i+1) t ∧
 word t.mem B (8*sD)=BitVec.ofNat 64 (VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i) ∧
 Outside B (8*sD) 8 s.mem t.mem ∧ Keep mmRegs s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.digit
 rw [WP.seq_iff]
 refine WP.mono (digitArgs_ok good room controls counter (by omega_using [positions])) ?_
 rintro u ⟨⟨ptr,len,row,spacing,width,zero,memU⟩,restU⟩
 rw [WP.seq_iff]
 refine WP.mono (gather_ok u (source.of_mem memU restU) size widthBound positions
  ptr len row width spacing zero) ?_
 rintro z ⟨digit,memZ,restZ⟩
 have mem : z.mem=s.mem := memZ.trans memU
 have goodZ : Good z B Z w mi :=
  ⟨good.scr.congr (restU.trans restZ).wr,((restU.trans restZ).gpr .x0 (by simp [gatherClobbers])).trans good.x0,mem ▸ good.hdr⟩
 refine WP.mono (store_control_ok goodZ room (by decide : 16≤sD) (by decide : sD<32) .x16) ?_
 rintro t ⟨goodT,memT,frameT,restT⟩
 have frame : Outside B (8*sD) 8 s.mem t.mem := by rw [←mem];exact frameT
 refine ⟨goodT,controls.after_digit frame,?_,?_,frame,((restU.trans restZ).trans restT).mono (by simp [gatherClobbers,mmRegs])⟩
 · exact (header_other frame (by decide) (by decide) (by decide)).trans counter
 · rw [memT,word_writeW_self,digit,prefixValue_eq_digit bs N i widthBound bound]

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! One proved comb row doubles the running exponent and adds one five-tooth entry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure Running (p : Parameters) (bs : List Byte) (E i : Nat) (s : State) : Prop where
 power : Power p E s
 controls : Controls p.B p.src p.ctx bs.length p.N s
 counter : Counter p.B i s
 tablePointer : TablePointer p.B p.table s
 reads : ReadEnv p bs s

theorem Running.after_arrays {p : Parameters} {bs : List Byte} {E E' i : Nat} {s t : State} {js : List Nat}
 (h : Running p bs E i s) (power : Power p E' t) (frame : Arrays p.B p.w js s.mem t.mem)
 (rest : Keep mmRegs s t) (within : ∀ j∈js,j<8) : Running p bs E' i t :=
 ⟨power,h.controls.after_arrays frame,(arrays_header frame (by decide)).trans h.counter,
  (arrays_header frame (by decide)).trans h.tablePointer,h.reads.after_arrays frame rest within⟩

theorem running_step (M : Mont) {p : Parameters} {bs : List Byte} {E i : Nat} {s : State}
 (h : Running p bs E (i+1) s) (size : bs.length<2^31) (widthBound : p.N≤8*bs.length)
 (positions : i+5*Spec.Rsa.FixedBaseComb.rows p.N<2^63) (bound : Spec.Rsa.os2ip bs<2^p.N) :
 WP isa (Comb.step M.mm) s fun t =>
 Running p bs (2*E+Spec.Rsa.FixedBaseComb.exponent p.N (VG.Proof.Rsa.FixedBaseComb.digit p.N (Spec.Rsa.os2ip bs) i)) i t ∧
 StableHeader p.B s.mem t.mem ∧ t.gpr .x3=BitVec.ofNat 64 i ∧ Keep mmRegs s t := by
 unfold Comb.step
 rw [WP.seq_iff]
 refine WP.mono (power_square M h.power) ?_
 rintro a ⟨powerA,frameA,keepA⟩
 have hA := h.after_arrays powerA frameA keepA (by simp)
 rw [WP.seq_iff]
 refine WP.mono (digit_ok powerA.good p.room hA.controls hA.counter hA.reads.source
  size widthBound positions bound) ?_
 rintro b ⟨goodB,controlsB,counterB,digitB,frameB,keepB⟩
 have powerB := powerA.after_header goodB frameB (by decide : sD<32)
 have readsB := hA.reads.after_header frameB keepB (by decide : sD<32)
 have tableB : TablePointer p.B p.table b :=
  (header_other frameB (by decide) (by decide) (by decide)).trans hA.tablePointer
 rw [WP.seq_iff]
 let v := VG.Proof.Rsa.FixedBaseComb.digit p.N (Spec.Rsa.os2ip bs) i
 have hv : v<32 := VG.Proof.Rsa.FixedBaseComb.digit_lt _ _ _
 refine WP.mono (select_ok goodB p.room (by have := p.positive;omega_using [this]) p.width hv tableB digitB
  readsB.tableRead readsB.tableOutside) ?_
 rintro c ⟨goodC,selectedC,frameC,keepC⟩
 have powerC := powerB.after_arrays goodC frameC (by decide) (by decide) (by decide) (by decide)
 have selected : wv c.mem p.B (slot p.w 5) p.w=
  Spec.Rsa.powMod p.G (Spec.Rsa.FixedBaseComb.exponent p.N v) p.P*2^(64*p.w)%p.P :=
  selectedC.trans (readsB.table v hv)
 have runB : Running p bs (2*E) (i+1) b := ⟨powerB,controlsB,counterB,tableB,readsB⟩
 have runC := runB.after_arrays powerC frameC keepC (by simp)
 rw [WP.seq_iff]
 refine WP.mono (power_product M powerC selected) ?_
 rintro d ⟨powerD,frameD,keepD⟩
 have runD := runC.after_arrays powerD frameD keepD (by simp)
 refine WP.mono (decrement_control_ok powerD.good p.room (by decide : 16≤sI) (by decide : sI<32)
  (by omega_using [] : 0<i+1) runD.counter) ?_
 rintro t ⟨goodT,counterT,indexT,frameT,keepT⟩
 have powerT := powerD.after_header goodT frameT (by decide : sI<32)
 have tableT : TablePointer p.B p.table t :=
  (header_other frameT (by decide) (by decide) (by decide)).trans runD.tablePointer
 refine ⟨⟨powerT,runD.controls.after_counter frameT,?_,tableT,
  runD.reads.after_header frameT keepT (by decide : sI<32)⟩,?_,?_,
  ((((keepA.trans keepB).trans keepC).trans keepD).trans keepT).mono (by decide)⟩
 · simpa only [Counter,Nat.add_sub_cancel] using counterT
 · exact ((((StableHeader.of_arrays frameA).trans (StableHeader.of_control frameB (Or.inr (Or.inl rfl)))).trans
    (StableHeader.of_arrays frameC)).trans (StableHeader.of_arrays frameD)).trans
    (StableHeader.of_control frameT (Or.inl rfl))
 · simpa only [Nat.add_sub_cancel] using indexT

end VG.Proof.Ffdh.AArch64.Cached
