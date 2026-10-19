module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowSCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Loop
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tile
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideGeneral
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareDispatch
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsChoiceCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Word
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxHeaderCopy
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Frame
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowS
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8RowSCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tile
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonal
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalChoice
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideGeneral
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRawCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareDispatch
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCrossCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRowsChoiceCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTail
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledTailSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Block
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Math
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCore
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Word
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# `vg_rsa_mont_mul_adx` as the Montgomery multiplication of the RSA code

Calls of `vg_rsa_mont_mul_adx`, inlined (`Mont.fnAdx`), for the proofs of
its callers (`Verified.of_inline`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The call of `vg_rsa_mont_mul_adx`, inlined: what calls of it run as. -/
def mmFnAdx (o a b : Nat) : Prog isa := (call "vg_rsa_mont_mul_adx" mulAdx o a b).inline

theorem mmFnAdx_eq (o a b : Nat) : mmFnAdx o a b = .seq (.block (args o a b)) mulAdx := rfl

theorem mmFnAdx_ct {o a b : Nat} (op : Opnds o a b) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.seq (.block (args o a b)) (.block (enter ++ slotsIn))) hc).isSome = true) :
    RelCT isa (Two GoodW) (mmFnAdx o a b) fun _ _ => True := by
  rw [mmFnAdx_eq]
  unfold mulAdx
  refine RelCT.assoc (RelCT.seq (two_piece (Ψ := fun L s => AdxMid ⟨L.B, L.Z, L.w, o, a, b⟩ s) [.rdi] pins_goodW h
    fun L s ⟨_, hg, hZ⟩ => ?_) (two_map (fun L : Ws => (⟨L.B, L.Z, L.w, o, a, b⟩ : CallData)) (fun _ _ h => h)
      adxTail_ct))
  refine WP.seq (WP.mono (fnArgs_ok s o a b) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
  exact WP.mono (adxHead_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ op.1 op.2.1
    op.2.2.1 hdx hcx h8) fun u ⟨hm', hdx', hcx', h8', k', _⟩ =>
      AdxMid.of_head (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ op hm' hdx' hcx' h8' k'

/-- Montgomery multiplication by calls of `vg_rsa_mont_mul_adx`, as inlined code. -/
def Mont.fnAdx : Mont where
  mm := mmFnAdx
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 d5 d4 d6 hinv hB := by
    rw [mmFnAdx_eq]
    refine WP.seq (WP.mono (fnArgs_ok _ _ _ _) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
    rw [← hm] at hinv hB ⊢
    refine WP.mono (mulAdx_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ hw hw'
      ho ha hb d1 d2 d3 d5 d4 d6 hdx hcx h8 hinv hB) fun t' ⟨h1, h2, h3, k', _⟩ => ?_
    exact ⟨⟨hg.scr.congr ((k.trans k').2.2), ((k.trans k').gpr (by decide)).trans hg.rdi, h3.hdr (hm ▸ hg.hdr)⟩,
      h1, h2, h3, (k.trans k').mono (by decide)⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact mmFnAdx_ct (by unfold Opnds; decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
