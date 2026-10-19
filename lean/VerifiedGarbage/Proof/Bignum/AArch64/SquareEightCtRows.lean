module

public import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtOff
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCtOff
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Impl.Bignum.AArch64
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks)

abbrev RowPre (a : Nat) (p : Ws × Nat) (s : State) := p.2 < blocks p.1 ∧ LoopCtx a p.1 p.2 s

theorem pins_row (a : Nat) : Pins (RowPre a) [.x0] :=
  fun p s t hs ht => pins_goodW p.1 s t hs.2.fast.1 ht.2.fast.1

theorem pins_basic (a : Nat) : Pins (BasicCtx a) [.x0] :=
  fun p s t hs ht => pins_goodW p.1 s t hs.fast.1 ht.fast.1

theorem pins_internal (a : Nat) : Pins (InternalCtx a) [.x8, .x16] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.ptrs.basic.ptr.trans ht.ptrs.basic.ptr.symm
  · exact hs.ptrs.tptr.trans ht.ptrs.tptr.symm

theorem pins_after_internal (a : Nat) : Pins (AfterInternal a) [.x0] :=
  fun p s t hs ht => pins_basic a p s t hs.1 ht.1

theorem pins_head (a : Nat) : Pins (HeadCtx a) [.x8, .x16, .x17, .x15] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.ptrs.basic.ptr.trans ht.ptrs.basic.ptr.symm
  · exact hs.ptrs.tptr.trans ht.ptrs.tptr.symm
  · exact hs.ptrs.nptr.trans ht.ptrs.nptr.symm
  · exact hs.iterations.trans ht.iterations.symm

theorem pins_tail (a : Nat) : Pins (PtrCtx a true) [.x8, .x12, .x16] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.basic.ptr.trans ht.basic.ptr.symm
  · exact hs.basic.count.trans ht.basic.count.symm
  · exact hs.tptr.trans ht.tptr.symm

theorem head_ct {a : Nat} (ha : a < 8)
    {ho hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true) :
    RelCT isa (Two (RowPre a)) (.block (SquareEightRaw.rowHead a)) (Two (HeadCtx a)) := by
  have heq : SquareEightRaw.rowHead a =
      (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a ++ headInternal) ++ headSuffix a := by
    simp only [SquareEightRaw.rowHead, headInternal, headSuffix, List.append_assoc]
  rw [heq]
  apply RelCT.block_append
  refine RelCT.seq ?_ (two_piece _ (pins_after_internal a) hH (head_suffix_ctx ha))
  apply RelCT.block_append
  exact RelCT.seq (two_piece _ (pins_row a) hO (initial_ptr_ctx ha))
    (two_piece _ (pins_internal a) (by taint_decide) (internal_ctx ha))

theorem tail_ct {a : Nat} (ha : a < 8)
    {ho : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true) :
    RelCT isa (Two (BasicCtx a)) (.block (SquareEightRaw.rowTail a)) (fun _ _ => True) := by
  have heq : SquareEightRaw.rowTail a =
      VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a ++ tailFinish := by
    simp only [SquareEightRaw.rowTail, tailFinish, List.append_assoc]
  rw [heq]
  apply RelCT.block_append
  exact RelCT.seq (two_piece _ (pins_basic a) hO
    (fun p s h => WP.mono (output_ctx_mem ha true p s h) fun _ ht => ht.1))
    (two_taint _ (pins_tail a) (by taint_decide))

theorem row_ct {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    {ho hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true) :
    RelCT isa (Two (RowPre a)) (rowBody a) (fun _ _ => True) := by
  unfold rowBody
  exact RelCT.seq (head_ct ha hO hH)
    (RelCT.seq (two_post (two_taint _ (pins_head a) (by taint_decide)) (off_ctx ha ha1 ha2))
      (tail_ct ha hO))

theorem rows_ct {a : Nat} (ha : a < 8) (ha1 : a ≠ Public.aAcc) (ha2 : a ≠ Public.aTmp)
    {ho hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hO : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.outputPtr true a)) ho).isSome = true)
    (hH : (taint.check (Taint.ofRegs [.x0]) (.block (headSuffix a)) hh).isSome = true) :
    RelCT isa (Two fun L s => 0 < blocks L ∧ LoopCtx a L 0 s)
      (SquareEightRaw.rows a) (Two fun L s => LoopCtx a L (blocks L) s) := by
  apply two_loop blocks (row_ct ha ha1 ha2 hO hH)
  intro L j s hj h
  refine WP.mono (row_ctx_next ha ha1 ha2 hj h) fun t ⟨ht, he⟩ => ⟨he, fun _ => ht, ?_⟩
  intro hlast
  exact hlast ▸ ht

end VG.Proof.Bignum.AArch64.SquareEight
