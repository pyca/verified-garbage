module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.StorePrefixTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.TableTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratorContextFrame
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! The complete public-context serialization and comb-table tail. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem prefix_table_ready {q : TablePublic} {s : State} (h : TableReady q s) :
 WP isa Precompute.storePrefix s (TableReady q) := by
 refine WP.mono (storePrefix_ok h.field h.space h.context) ?_
 rintro t ⟨field,_,_,frame,same,rest⟩
 have hdr (i : Nat) (hi : i<32) :=workspace_header h.field.good same hi
 exact ⟨⟨field,h.space.after rest,h.generator.after_context frame (by omega) rest,
  (hdr sCtx (by decide)).trans h.context,(hdr sDom (by decide)).trans h.domain,
  (hdr sLen (by decide)).trans h.length⟩,(hdr sRows (by decide)).trans h.rows⟩

theorem precomputeTail_ct (M : Mont) : RelCT isa (Two TableReady)
 (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1]))) (fun _ _ =>True) := by
 refine RelCT.seq (two_post
  (two_map (fun q =>q.p) (fun _ _ h =>⟨h.field.good,h.space,h.context⟩) storePrefix_ct)
  (fun _ _ h =>prefix_table_ready h)) ?_
 refine RelCT.seq (two_post (Ψ:=fun (_ : TablePublic) _ =>True) (precomputeTable_ct M) ?_)
  (two_taint [] (fun _ _ _ _ _ r hr =>by simp at hr) (by taint_decide))
 intro q s h
 exact WP.mono (precomputeTable_ok M h.field h.space h.generator q.words q.positive q.size q.reduced q.bits h.context h.domain h.length h.rows)
  (fun _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached
