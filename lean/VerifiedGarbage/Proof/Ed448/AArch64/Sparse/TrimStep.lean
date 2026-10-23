module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.DigitLoads
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Magnitude
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Move
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyChecks
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode

/-! Leading-zero scanning stops at the first nonzero pair, including the all-zero pair. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off)

abbrev trimClob : List Reg := [.x19,.x2,.x11,.x7,.x9,.x4]

private theorem guard_fact : ∀ i<464,
    (BitVec.ofNat 64 i-(1#64))>>>63=(if i=0 then 1 else 0):=by decide +kernel

private theorem trimTail_ok {s:State} {i:Nat} (hi:i<464)
    (hc:s.gpr .x19=BitVec.ofNat 64 i) {ds dk:Int}
    (hsd:-127≤ds ∧ ds≤127) (hkd:-127≤dk ∧ dk≤127)
    (h7:s.gpr .x7=(BitVec.ofInt 8 ds).setWidth 64)
    (h11:s.gpr .x11=(BitVec.ofInt 8 dk).setWidth 64) :
    WP isa (.block [.logic .orr .x .x9 .x7 .x11,.subImm .x .x4 .x19 1,
      .lsr .x .x4 .x4 63,.logic .orr .x .x9 .x9 .x4]) s fun t =>
      (t.gpr .x9==0)=decide (ds=0 ∧ dk=0 ∧ i≠0) ∧ Keeps [.x9,.x4] s t ∧ t.mem=s.mem:=by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,Nat.reduceLT,
    ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,h7,h11,hc,guard_fact i hi,
    ite_false,reduceCtorEq,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl⟩,rfl⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,decide_eq_true_eq,VG.Proof.Ed448.AArch64.or_eq_zero64]
    have hs:=encoded_zero hsd
    have hk:=encoded_zero hkd
    have hs':((BitVec.ofInt 8 ds).setWidth 64=0)↔ds=0:=by
      simpa only [beq_iff_eq,decide_eq_true_eq] using Bool.eq_iff_iff.mp hs
    have hk':((BitVec.ofInt 8 dk).setWidth 64=0)↔dk=0:=by
      simpa only [beq_iff_eq,decide_eq_true_eq] using Bool.eq_iff_iff.mp hk
    rw [hs',hk']
    by_cases hz:i=0 <;> simp [hz]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem trimStep_ok {s:State} {base:Addr} (hs:Scr s base) {i:Nat} (hi:i<464)
    (hc:s.gpr .x19=BitVec.ofNat 64 (i+1)) {ds dk:Int}
    (hsd:-127≤ds ∧ ds≤127) (hkd:-127≤dk ∧ dk≤127)
    (hbs:s.mem (off base (SDIG+i))=BitVec.ofInt 8 ds)
    (hbk:s.mem (off base (BITS+i))=BitVec.ofInt 8 dk) :
    WP isa (.block trimStep) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 i ∧
      (t.gpr .x9==0)=decide (ds=0 ∧ dk=0 ∧ i≠0) ∧ Keeps trimClob s t ∧ t.mem=s.mem:=by
  have he:trimStep=[.subImm .x .x19 .x19 1]++(baseDigit++([.addImm .x .x7 .x11 0]++
      (keyDigit++[.logic .orr .x .x9 .x7 .x11,.subImm .x .x4 .x19 1,
        .lsr .x .x4 .x4 63,.logic .orr .x .x9 .x9 .x4]))):=by simp only [trimStep,List.append_assoc]
  rw [he,WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.decCounter_ok (by omega) hc)
    fun a ⟨a19,ag,am,ar,aw,_⟩ => ?_
  have ak:Keeps [.x19] s a:=⟨fun r hr => ag r (by simpa only [List.mem_singleton] using hr),ar,aw⟩
  have ha:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (baseDigit_ok ha hi a19) fun b ⟨b11,bk,bm⟩ => ?_
  have hb:=ha.of_keeps bk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (Window.mov_ok .x7 .x11 b) fun c ⟨c7,cm,ck⟩ => ?_
  have hc':=hb.of_keeps ck (by decide)
  rw [WP.block_append_iff]
  have c19:c.gpr .x19=BitVec.ofNat 64 i:=(ck.1 _ (by decide)).trans ((bk.1 _ (by decide)).trans a19)
  refine WP.mono (keyDigit_ok hc' hi c19) fun d ⟨d11,dk',dm⟩ => ?_
  have d19:d.gpr .x19=BitVec.ofNat 64 i:=(dk'.1 _ (by decide)).trans c19
  have d7:d.gpr .x7=(BitVec.ofInt 8 ds).setWidth 64:=by
    rw [dk'.1 _ (by decide),c7,b11,am,hbs]
  have d11':d.gpr .x11=(BitVec.ofInt 8 dk).setWidth 64:=by rw [d11,cm,bm,am,hbk]
  refine WP.mono (trimTail_ok hi d19 hsd hkd d7 d11') fun t ⟨tz,tk,tm⟩ => ?_
  refine ⟨(tk.1 _ (by decide)).trans d19,tz,?_,?_⟩
  · have k1:Keeps trimClob s b:=(ak.mono (by decide)).trans (bk.mono (by decide))
    have k2:Keeps trimClob b d:=(ck.mono (by decide)).trans (dk'.mono (by decide))
    exact (k1.trans k2).trans (tk.mono (by decide))
  · rw [tm,dm,cm,bm,am]

end VG.Proof.Ed448.AArch64.Sparse
