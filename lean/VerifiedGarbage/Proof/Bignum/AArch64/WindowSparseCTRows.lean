module

public import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseCtHead
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.WindowSparseCtHead
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtRows
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks)

abbrev RowPre (a : Nat) (p : Ws × Nat) (s : State) := p.2 < blocks p.1 ∧ LoopCtx a p.1 p.2 s

theorem pins_row (a : Nat) : Pins (RowPre a) [.x0] :=
  fun p s t hs ht => pins_goodW p.1 s t hs.2.fast.1 ht.2.fast.1

open VG.Proof.Bignum.AArch64.SquareEight (BasicCtx PtrCtx HeadCtx AfterInternal pins_after_internal pins_head head_suffix_ctx tail_ct off_ctx)

theorem pins_internal (a : Nat) : Pins (PtrCtx a true) [.x8,.x16] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.basic.ptr.trans ht.basic.ptr.symm
  · exact hs.tptr.trans ht.tptr.symm

theorem head_ct {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    {ho hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true) :
    RelCT isa (Two (RowPre a)) (.block (VG.Impl.Bignum.AArch64.WindowSparse.rowHead a)) (Two (HeadCtx a)) := by
  have heq : VG.Impl.Bignum.AArch64.WindowSparse.rowHead a =
      (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a ++ headInternal) ++ headSuffix a := by
    simp only [VG.Impl.Bignum.AArch64.WindowSparse.rowHead, headInternal, headSuffix, List.append_assoc]
  rw [heq]
  apply RelCT.block_append
  refine RelCT.seq ?_ (two_piece _ (pins_after_internal a) hH (head_suffix_ctx ha))
  apply RelCT.block_append
  exact RelCT.seq (two_piece _ (pins_row a) hO (initial_ptr_ctx ha))
    (two_piece _ (pins_internal a) (by taint_decide) (internal_ctx ha ha1 ha2))

theorem row_ct {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    {ho hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true) :
    RelCT isa (Two (RowPre a)) (rowBody a) (fun _ _ => True) := by
  unfold rowBody
  exact RelCT.seq (head_ct ha ha1 ha2 hO hH)
    (RelCT.seq (two_post (two_taint _ (pins_head a) (by taint_decide)) (off_ctx ha ha1 ha2))
      (tail_ct ha hO))

theorem rows_ct {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    {ho hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true) :
    RelCT isa (Two fun L s => 0 < blocks L ∧ LoopCtx a L 0 s)
      (VG.Impl.Bignum.AArch64.WindowSparse.rows a) (Two fun L s => LoopCtx a L (blocks L) s) := by
  apply two_loop blocks (row_ct ha ha1 ha2 hO hH)
  intro L j s hj h
  refine WP.mono (row_ctx_next ha ha1 ha2 hj h) fun t ⟨ht, he⟩ => ⟨he, fun _ => ht, ?_⟩
  intro hlast
  exact hlast ▸ ht

end VG.Proof.Bignum.AArch64.WindowSparse
