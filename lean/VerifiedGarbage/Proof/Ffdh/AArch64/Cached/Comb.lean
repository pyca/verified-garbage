module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Step
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Ffdh.AArch64.Cached.InitControls`, which only this module used -/

section

/-! Store the policy's exact row count and canonical packed-table pointer. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem counter_ok {p : Parameters} {bs : List Byte} {s : State}
 (good : Good s p.B p.Z p.w p.mi) (controls : Controls p.B p.src p.ctx bs.length p.N s) :
 WP isa (.block Comb.initCounter) s fun t =>
 Good t p.B p.Z p.w p.mi ∧ Counter p.B (Spec.Rsa.FixedBaseComb.rows p.N) t ∧
 Outside p.B (8*sI) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 unfold Comb.initCounter
 refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.mem=s.mem.writeW (off p.B (8*sI))
  (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sI<32 by decide),hdr_enc (show sRows<32 by decide),
   header_read good p.room (show sRows<32 by decide),controls.rows,
   good.scr.st (d:=8*sI) (by have := hdr_lt_slot p.w 8 (show sI<32 by decide);have := p.room;omega_arith)]
 · rintro t ⟨mem,rest⟩
   have frame : Outside p.B (8*sI) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by decide)
   refine ⟨good_after_header good (by decide) (by decide) frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   unfold Counter
   rw [mem,word_writeW_self]

private theorem table_ok {p : Parameters} {bs : List Byte} {s : State}
 (good : Good s p.B p.Z p.w p.mi) (controls : Controls p.B p.src p.ctx bs.length p.N s)
 (pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w)) :
 WP isa (.block Comb.initTable) s fun t =>
 Good t p.B p.Z p.w p.mi ∧ TablePointer p.B p.table t ∧
 Outside p.B (8*sTab) 8 s.mem t.mem ∧ Keep [.x3,.x4] s t := by
 have shift : BitVec.ofNat 64 p.w <<< 4=BitVec.ofNat 64 (16*p.w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  have := p.width
  omega_using []
 have address : (p.ctx+(BitVec.ofNat 64 p.w <<< 4))+24#64=p.table := by
  rw [shift,pointer,BitVec.add_assoc,show (24#64:Addr)=BitVec.ofNat 64 24 from rfl,←BitVec.ofNat_add]
  congr 2
  omega_using []
 unfold Comb.initTable
 refine WP.mono (WP.keep [.x3,.x4] (Q:=fun t =>t.mem=s.mem.writeW (off p.B (8*sTab)) p.table)
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sCtx<32 by decide),hdr_enc (show sW<32 by decide),hdr_enc (show sTab<32 by decide),
   header_read good p.room (show sCtx<32 by decide),header_read good p.room (show sW<32 by decide),
   good.hdr.hw,controls.context,address,
   good.scr.st (d:=8*sTab) (by have := hdr_lt_slot p.w 8 (show sTab<32 by decide);have := p.room;omega_arith)]
 · rintro t ⟨mem,rest⟩
   have frame : Outside p.B (8*sTab) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by decide)
   refine ⟨good_after_header good (by decide) (by decide) frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   unfold TablePointer
   rw [mem,word_writeW_self]

theorem init_controls {p : Parameters} {bs : List Byte} {s : State}
 (power : Power p 0 s) (controls : Controls p.B p.src p.ctx bs.length p.N s) (reads : ReadEnv p bs s)
 (pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w)) :
 WP isa (.seq (.block Comb.initCounter) (.block Comb.initTable)) s fun t =>
 Running p bs 0 (Spec.Rsa.FixedBaseComb.rows p.N) t ∧ StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t := by
 rw [WP.seq_iff]
 refine WP.mono (counter_ok power.good controls) ?_
 rintro u ⟨goodU,counterU,frameU,keepU⟩
 have powerU := power.after_header goodU frameU (by decide : sI<32)
 have controlsU := controls.after_counter frameU
 have readsU := reads.after_header frameU keepU (by decide : sI<32)
 refine WP.mono (table_ok goodU controlsU pointer) ?_
 rintro t ⟨goodT,tableT,frameT,keepT⟩
 refine ⟨⟨powerU.after_header goodT frameT (by decide : sTab<32),controlsU.after_table frameT,?_,tableT,
  readsU.after_header frameT keepT (by decide : sTab<32)⟩,?_,(keepU.trans keepT).mono (by decide)⟩
 · exact (header_other frameT (by decide) (by decide) (by decide)).trans counterU
 · exact (StableHeader.of_control frameU (Or.inl rfl)).trans (StableHeader.of_control frameT (Or.inr (Or.inr rfl)))

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The complete native cached exponentiation, from canonical R² to ordinary g^x. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/Loop.lean`, which only this module imported.
section

/-! The complete fixed public row schedule reconstructs the unrevealed scalar. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Spec.Rsa.FixedBaseComb (rows exponent)
open VG.Proof.Rsa.FixedBaseComb (high high_step high_top high_zero rows_pos rows_small)

theorem comb_loop (M : Mont) {p : Parameters} {bs : List Byte} {s : State}
 (start : Running p bs 0 (rows p.N) s) (positive : 0<p.N) (width : p.N≤8192)
 (size : bs.length<2^31) (widthBound : p.N≤8*bs.length) (bound : Spec.Rsa.os2ip bs<2^p.N) :
 WP isa (.loop (Comb.step M.mm) (.nonzero .x .x3)) s fun t =>
 Running p bs (Spec.Rsa.os2ip bs) 0 t ∧ StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t := by
 let x := Spec.Rsa.os2ip bs
 let d := rows p.N
 have dPositive : 0<d := rows_pos positive
 have dBound : d≤1639 := (rows_small width).1
 let I := fun n t => 0<n ∧ n≤d ∧ Running p bs (high p.N x n) n t ∧
  StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t
 refine WP.loop (M:=isa) I ?_ d s ?_
 · intro n t h
   obtain ⟨nPositive,nBound,run,stable,keep⟩ := h
   have eq : n=(n-1)+1 := by omega_using [nPositive]
   have rowBound : n-1<rows p.N := by change n-1<d;omega_using [dPositive, nBound]
   have input : Running p bs (high p.N x ((n-1)+1)) ((n-1)+1) t := by rw [←eq];exact run
   refine WP.mono (running_step M input size widthBound (by change n-1+5*d<2^63;omega_using [dBound, nBound]) bound) ?_
   rintro u ⟨runU,stableU,indexU,keepU⟩
   have powerEq := high_step p.N x (n-1) rowBound
   rw [←powerEq] at runU
   have totalStable := stable.trans stableU
   have totalKeep : Keep mmRegs s u := (keep.trans keepU).mono (by simp)
   by_cases last : n=1
   · left
     refine ⟨?_,?_,totalStable,totalKeep⟩
     · rw [eval_nonzero,indexU]
       change some (BitVec.ofNat 64 (n-1) != 0#64)=some false
       subst n;decide
     · simpa only [last,Nat.sub_self,high_zero p.N x bound] using runU
   · right
     refine ⟨?_,n-1,by omega_using [nPositive],by omega_using [nPositive, last],by omega_using [nBound],runU,totalStable,totalKeep⟩
     rw [eval_nonzero,indexU]
     change some (BitVec.ofNat 64 (n-1) != 0#64)=some true
     rw [ofNat_nonzero (by omega_using [dBound, nBound] : n-1<2^64),decide_eq_true (by omega_using [nPositive, last] : 0<n-1)]
 · refine ⟨dPositive,Nat.le_refl _,?_,StableHeader.refl _ _,Keep.refl _ _⟩
   simpa only [d,high_top] using start

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/Decode.lean`, which only this module imported.
section

/-! Conversion out of Montgomery form produces exactly the ordinary public value. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem power_decode (M : Mont) {p : Parameters} {E : Nat} {s : State} (h : Power p E s) :
 WP isa (M.mm 6 6 7) s fun t =>
 ModState p t ∧ wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P ∧
 Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 have bound7 : wv s.mem p.B (slot p.w 7) p.w<p.P := by rw [h.one];exact p.modulusPositive
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 6<8) (by decide : 7<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse bound7) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frame,rest⟩
 have modT := h.toModState.after_arrays goodT frame (by decide) (by decide) (by decide)
 have eq : wv t.mem p.B (slot p.w 6) p.w*2^(64*p.w)%p.P=
  Spec.Rsa.powMod p.G E p.P*2^(64*p.w)%p.P := by
  simpa only [h.one,h.value,Nat.mul_one,Nat.mod_mod] using productT
 have cancel := VG.Proof.Bignum.mont_cancel p.coprime eq
 rw [Nat.mod_eq_of_lt boundT] at cancel
 have decoded : wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P := by
  simpa only [VG.Proof.Bignum.powMod_eq,Nat.mod_mod] using cancel
 exact ⟨modT,decoded,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem reassoc {a b c : Prog isa} {s : State} {Q : State → Prop} :
 WP isa (.seq a (.seq b c)) s Q ↔ WP isa (.seq (.seq a b) c) s Q := by
 exact ⟨WP.assoc',WP.assoc⟩

theorem comb_correct (M : Mont) {p : Parameters} {bs : List Byte} {s : State}
 (start : Initial p bs s) (positive : 0<p.N) (width : p.N≤8192)
 (size : bs.length<2^31) (widthBound : p.N≤8*bs.length) (bound : Spec.Rsa.os2ip bs<2^p.N)
 (pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w)) :
 WP isa (VG.Impl.Ffdh.AArch64.Cached.Comb.code M.mm) s fun t =>
 ModState p t ∧ wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G (Spec.Rsa.os2ip bs) p.P ∧
 Controls p.B p.src p.ctx bs.length p.N t ∧ ReadEnv p bs t ∧
 StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.code
 rw [reassoc,WP.seq_iff]
 refine WP.mono (initial_power M start) ?_
 rintro a ⟨powerA,controlsA,readsA,stableA,keepA⟩
 rw [reassoc,WP.seq_iff]
 refine WP.mono (init_controls powerA controlsA readsA pointer) ?_
 rintro b ⟨runB,stableB,keepB⟩
 rw [WP.seq_iff]
 refine WP.mono (comb_loop M runB positive width size widthBound bound) ?_
 rintro c ⟨runC,stableC,keepC⟩
 refine WP.mono (power_decode M runC.power) ?_
 rintro t ⟨modT,valueT,frameT,keepT⟩
 exact ⟨modT,valueT,runC.controls.after_arrays frameT,runC.reads.after_arrays frameT keepT (by simp),
  ((stableA.trans stableB).trans stableC).trans (StableHeader.of_arrays frameT),
  (((keepA.trans keepB).trans keepC).trans keepT).mono (by simp)⟩

end VG.Proof.Ffdh.AArch64.Cached
