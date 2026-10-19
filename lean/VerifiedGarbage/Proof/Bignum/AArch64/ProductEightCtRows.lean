module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtContext
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.BlockedRedc (FastW blocks)

abbrev RowPre (a b : Nat) (p : Ws × Nat) (s : State) :=
  p.2 < blocks p.1 ∧ LoopCtx a b p.1 p.2 s

theorem pins_loop (a b : Nat) : Pins (RowPre a b) [.x0] :=
  fun p s t hs ht => pins_goodW p.1 s t hs.2.fast.1 ht.2.fast.1

theorem pins_head (a b : Nat) : Pins (HeadCtx a b) [.x8, .x12, .x16, .x17, .x15] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hs.loop.ptr.trans ht.loop.ptr.symm
  · exact hs.loop.count.trans ht.loop.count.symm
  · exact hs.tptr.trans ht.tptr.symm
  · exact hs.nptr.trans ht.nptr.symm
  · exact hs.count.trans ht.count.symm

theorem row_ct {a b : Nat} (ha : a < 8) (hb : b < 8)
    {hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hH : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.rowSetup a b)) hh).isSome = true) :
    RelCT isa (Two (RowPre a b)) (rowBody a b) (fun _ _ => True) := by
  unfold rowBody
  exact RelCT.seq (two_piece [.x0] (pins_loop a b) hH (head_ctx ha hb))
    (two_taint _ (pins_head a b) (by taint_decide))

theorem rows_ct {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ VG.Impl.Bignum.Public.aAcc) (ha2 : a ≠ VG.Impl.Bignum.Public.aTmp)
    (hb1 : b ≠ VG.Impl.Bignum.Public.aAcc) (hb2 : b ≠ VG.Impl.Bignum.Public.aTmp)
    {hh : VG.Taint.Hint VG.AArch64.Taint.T}
    (hH : (taint.check (Taint.ofRegs [.x0])
      (.block (VG.Impl.Bignum.AArch64.ProductEight.rowSetup a b)) hh).isSome = true) :
    RelCT isa (Two fun L s => 0 < blocks L ∧ LoopCtx a b L 0 s)
      (VG.Impl.Bignum.AArch64.ProductEight.rows a b)
      (Two fun L s => LoopCtx a b L (blocks L) s) := by
  apply two_loop blocks (row_ct ha hb hH)
  intro L j s hj h
  refine WP.mono (row_ctx_next ha hb ha1 ha2 hb1 hb2 hj h) fun t ⟨ht, he⟩ =>
    ⟨he, fun _ => ht, ?_⟩
  intro hlast
  exact hlast ▸ ht

end VG.Proof.Bignum.AArch64.ProductEight
