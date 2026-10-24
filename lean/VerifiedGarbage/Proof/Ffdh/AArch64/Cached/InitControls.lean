module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Step
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

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
   good.scr.st (d:=8*sI) (by have := hdr_lt_slot p.w 8 (show sI<32 by decide);have := p.room;omega)]
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
  omega
 have address : (p.ctx+(BitVec.ofNat 64 p.w <<< 4))+24#64=p.table := by
  rw [shift,pointer,BitVec.add_assoc,show (24#64:Addr)=BitVec.ofNat 64 24 from rfl,←BitVec.ofNat_add]
  congr 2
  omega
 unfold Comb.initTable
 refine WP.mono (WP.keep [.x3,.x4] (Q:=fun t =>t.mem=s.mem.writeW (off p.B (8*sTab)) p.table)
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sCtx<32 by decide),hdr_enc (show sW<32 by decide),hdr_enc (show sTab<32 by decide),
   header_read good p.room (show sCtx<32 by decide),header_read good p.room (show sW<32 by decide),
   good.hdr.hw,controls.context,address,
   good.scr.st (d:=8*sTab) (by have := hdr_lt_slot p.w 8 (show sTab<32 by decide);have := p.room;omega)]
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
