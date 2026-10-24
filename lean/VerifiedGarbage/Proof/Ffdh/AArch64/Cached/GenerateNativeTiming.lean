module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.NativeTimingState
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Complete cached-attempt timing, including its original register and stack arguments. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def EntryLoaded (q : FrontPublic) (s : State) : Prop :=
 s.gpr .x0=q.body.scalar.p.src ∧ s.gpr .x2=q.body.yp ∧ s.gpr .x4=q.body.scalar.dp ∧
 s.gpr .x5=BitVec.ofNat 64 q.body.scalar.dl ∧ s.gpr .x6=BitVec.ofNat 64 q.body.scalar.p.k ∧
 s.gpr .x7=q.rp ∧ s.gpr .x8=q.body.scalar.p.B ∧ s.gpr .x9=q.body.scalar.p.ctx

theorem generateEntry_ct : RelCT isa (Two NativeReady) (.block Generate.entry) (fun _ _ =>True) := by
 change RelCT isa (Two NativeReady) (.block ((Generate.entry.take 2)++(Generate.entry.drop 2))) _
 apply RelCT.block_append
 refine RelCT.seq (two_piece (Ψ:=EntryLoaded) [] (fun _ _ _ _ _ r hr =>by simp at hr) (by taint_decide) ?_)
  (two_taint [.x0,.x2,.x4,.x5,.x6,.x7,.x8,.x9] ?_ (by taint_decide))
 · rintro q s ⟨rb,h⟩
   change WP isa (.block [.ldrSp .x8 8,.ldrSp .x9 24]) s _
   brun [exec_ldrSp_x' _ (show 8%8=0 ∧ 8<32768 by decide) h.stackB,
    exec_ldrSp_x' (s.write .x .x8 q.body.scalar.p.B) (show 24%8=0 ∧ 24<32768 by decide)
     (by simpa only [RegUpd.rd_write,RegUpd.wr_write,RegUpd.sp_write] using h.stackCtx),
    h.readB,h.readCtx,h.xArg,h.yArg,h.domArg,h.dlArg,h.lenArg,h.randArg]
   simp [EntryLoaded,RegUpd.gpr_write,h.xArg,h.yArg,h.domArg,h.dlArg,h.lenArg,h.randArg]
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.1.trans ht.2.2.1.symm
   · exact hs.2.2.2.1.trans ht.2.2.2.1.symm
   · exact hs.2.2.2.2.1.trans ht.2.2.2.2.1.symm
   · exact hs.2.2.2.2.2.1.trans ht.2.2.2.2.2.1.symm
   · exact hs.2.2.2.2.2.2.1.trans ht.2.2.2.2.2.2.1.symm
   · exact hs.2.2.2.2.2.2.2.trans ht.2.2.2.2.2.2.2.symm

theorem generateNative_ct (M : Mont) : RelCT isa (Two NativeReady) (Generate.code M.mm) (fun _ _ =>True) := by
 change RelCT isa (Two NativeReady) (.seq (.block Generate.entry) (generatePrepared M.mm)) _
 exact RelCT.seq (two_post generateEntry_ct (fun _ _ h =>native_front_ok h)) (generatePrepared_ct M)

end VG.Proof.Ffdh.AArch64.Cached
