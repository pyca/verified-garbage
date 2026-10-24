module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.EntryPointer
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Public entry addressing and fixed-length stores have no residue-dependent trace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure EntryReady (q : Parameters × Nat) (s : State) : Prop where
 good : Good s q.1.B q.1.Z q.1.w q.1.mi
 context : word s.mem q.1.B (8*sCtx)=q.1.ctx
 digit : s.gpr .x3=BitVec.ofNat 64 q.2

theorem storeEntryHead_ok {s : State} {p : Parameters} {j a : Nat}
 (h : EntryReady (p,j) s) (array : a<8) :
 WP isa (.block (entryPtr++[ldh .x16 (sArr a)])) s fun t =>
 t.gpr .x16=off p.B (slot p.w a) ∧ t.gpr .x17=off p.ctx (entryOffset p.w j) ∧
 t.gpr .x12=BitVec.ofNat 64 p.w := by
 rw [WP.block_append_iff]
 refine WP.mono (entryPtr_ok h.good p.room h.context h.digit) ?_
 rintro u ⟨⟨pointer,count,mem⟩,rest⟩
 have arrHdr : sArr a<32 := by unfold sArr;omega
 have good : Good s p.B p.Z p.w p.mi := h.good
 change u.gpr .x17=off p.ctx (entryOffset p.w j) at pointer
 change u.gpr .x12=BitVec.ofNat 64 p.w at count
 brun [rest.rd,rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,
  hdr_enc arrHdr,good.scr.ld (d:=8*sArr a) (by have := hdr_lt_slot p.w 8 arrHdr;have := p.room;omega),
  mem,good.hdr.harr a array,pointer,count]

theorem storeEntry_ct (a : Nat) (array : a<8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
 (check : (taint.check (Taint.ofRegs [.x0,.x3]) (.block (entryPtr++[ldh .x16 (sArr a)])) hc).isSome=true) :
 RelCT isa (Two EntryReady) (storeEntry a) (fun _ _ => True) := by
 unfold storeEntry
 refine RelCT.seq (two_piece (Ψ:=fun q s =>
  s.gpr .x16=off q.1.B (slot q.1.w a) ∧ s.gpr .x17=off q.1.ctx (entryOffset q.1.w q.2) ∧
  s.gpr .x12=BitVec.ofNat 64 q.1.w) [.x0,.x3] ?_ check (fun _ _ h =>storeEntryHead_ok h array))
  (two_taint [.x16,.x17,.x12] ?_ (by taint_decide))
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact hs.good.x0.trans ht.good.x0.symm
   · exact hs.digit.trans ht.digit.symm
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm

theorem loadEntryHead_ok {s : State} {p : Parameters} {j a : Nat}
 (h : EntryReady (p,j) s) (array : a<8) :
 WP isa (.block (entryPtr++[mov .x16 .x17,ldh .x17 (sArr a)])) s fun t =>
 t.gpr .x16=off p.ctx (entryOffset p.w j) ∧ t.gpr .x17=off p.B (slot p.w a) ∧
 t.gpr .x12=BitVec.ofNat 64 p.w := by
 rw [WP.block_append_iff]
 refine WP.mono (entryPtr_ok h.good p.room h.context h.digit) ?_
 rintro u ⟨⟨pointer,count,mem⟩,rest⟩
 have arrHdr : sArr a<32 := by unfold sArr;omega
 have good : Good s p.B p.Z p.w p.mi := h.good
 change u.gpr .x17=off p.ctx (entryOffset p.w j) at pointer
 change u.gpr .x12=BitVec.ofNat 64 p.w at count
 brun [rest.rd,rest.wr,(rest.gpr .x0 (by decide)).trans good.x0,
  hdr_enc arrHdr,good.scr.ld (d:=8*sArr a) (by have := hdr_lt_slot p.w 8 arrHdr;have := p.room;omega),
  mem,good.hdr.harr a array,pointer,count]

theorem loadEntry_ct (a : Nat) (array : a<8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
 (check : (taint.check (Taint.ofRegs [.x0,.x3])
  (.block (entryPtr++[mov .x16 .x17,ldh .x17 (sArr a)])) hc).isSome=true) :
 RelCT isa (Two EntryReady) (loadEntry a) (fun _ _ => True) := by
 unfold loadEntry
 refine RelCT.seq (two_piece (Ψ:=fun q s =>
  s.gpr .x16=off q.1.ctx (entryOffset q.1.w q.2) ∧ s.gpr .x17=off q.1.B (slot q.1.w a) ∧
  s.gpr .x12=BitVec.ofNat 64 q.1.w) [.x0,.x3] ?_ check (fun _ _ h =>loadEntryHead_ok h array))
  (two_taint [.x16,.x17,.x12] ?_ (by taint_decide))
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact hs.good.x0.trans ht.good.x0.symm
   · exact hs.digit.trans ht.digit.symm
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Ffdh.AArch64.Cached
