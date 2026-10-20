module

public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtContext
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtContext
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64

abbrev RowPre (p : Ws × Nat) (s : State) := p.2 < blocks p.1 ∧ LoopCtx p.1 p.2 s

theorem pins_loop : Pins RowPre [.x0, .x8, .x12, .x7] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact pins_goodW p.1 s t hs.2.fast.1 ht.2.fast.1 .x0 (by simp)
  · exact hs.2.ptr.trans ht.2.ptr.symm
  · exact hs.2.count.trans ht.2.count.symm
  · exact hs.2.zero.trans ht.2.zero.symm

theorem pins_head : Pins HeadCtx [.x0, .x8, .x12, .x7, .x17] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact pins_goodW p.1 s t hs.loop.fast.1 ht.loop.fast.1 .x0 (by simp)
  · exact hs.loop.ptr.trans ht.loop.ptr.symm
  · exact hs.loop.count.trans ht.loop.count.symm
  · exact hs.loop.zero.trans ht.loop.zero.symm
  · exact hs.modulus.trans ht.modulus.symm

theorem pins_body : Pins BodyCtx [.x8, .x12, .x16, .x17, .x15] := by
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hs.loop.ptr.trans ht.loop.ptr.symm
  · exact hs.loop.count.trans ht.loop.count.symm
  · exact hs.tptr.trans ht.tptr.symm
  · exact hs.nptr.trans ht.nptr.symm
  · exact hs.count.trans ht.count.symm

/-- Header loads are recaptured through their proven public values before
using them as addresses or loop bounds. Arithmetic values stay secret. -/
theorem firstBlock_ct : RelCT isa (Two RowPre) (.block (rowPrefix ++ rowMiddle)) (fun _ _ => True) := by
  apply RelCT.block_append
  exact RelCT.seq (two_piece [.x0, .x8, .x12, .x7] pins_loop (by taint_decide) prefix_ctx)
    (two_taint [.x0, .x8, .x12, .x7, .x17] pins_head (by taint_decide))

theorem rowBody_ct : RelCT isa (Two RowPre) rowBody (fun _ _ => True) := by
  rewrite [row_split]
  exact RelCT.seq (two_post firstBlock_ct firstBlock_ctx)
    (two_taint [.x8, .x12, .x16, .x17, .x15] pins_body (by taint_decide))

end VG.Proof.Bignum.AArch64.BlockedRedc
