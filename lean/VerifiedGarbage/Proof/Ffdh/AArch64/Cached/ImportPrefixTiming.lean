module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportDataTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Context import starts from arbitrary scratch contents, with a public limb geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem importPrefix_ct : RelCT isa (Two ImportReady) importPrefix (fun _ _ =>True) := by
 change RelCT isa (Two ImportReady) (.seq (.block VG.Impl.Rsa.AArch64.head) importData) _
 refine RelCT.seq (two_piece (Ψ:=ImportDataReady) [.x0] (fun q s t hs ht r hr =>by
  have eq : r= .x0 := by simpa using hr
  subst r;exact hs.base.trans ht.base.symm) (by taint_decide) ?_) importData_ct
 intro q s h
 refine WP.mono (head_ok h.scratch h.base (by rw [←q.words];exact q.room) (by have :=q.size;omega)
  (by change word s.mem q.workspace.B (8*Public.sK)=_;exact h.length)) ?_
 rintro t ⟨_,width,arrays,frame,rest⟩
 rw [←q.words] at width arrays
 have context : word t.mem q.workspace.B (8*sCtx)=q.ctx := by
  rw [frame.word_eq (by
   simp only [List.mem_cons,List.not_mem_nil,or_false]
   rintro _ (rfl|rfl) <;>decide) (by decide)]
  exact h.context
 exact ⟨⟨word t.mem q.workspace.B (8*sMinv),⟨h.scratch.congr rest.wr,
  (rest.gpr .x0 (by decide)).trans h.base,width,rfl,arrays⟩,q.room⟩,context,
  fun i hi =>by rw [rest.rd,rest.wr];exact h.readable i hi,h.outside⟩

end VG.Proof.Ffdh.AArch64.Cached
