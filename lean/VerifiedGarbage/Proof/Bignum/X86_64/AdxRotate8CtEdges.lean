module
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Edges
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Edges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRow
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8TileEdges
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Word
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRow
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

/-! Public header loads establish the pointers used by the edge blocks. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (WP.keep)

theorem setupBases_fw (L : Ws) (s : State) (h : GoodW L s) :
    WP isa (.block AdxRotate8.setupBases) s fun t => t.gpr .rcx = off L.B (slot L.w aAcc + 16) := by
  obtain ⟨mi, hg, hZ⟩ := h
  have hl := hg.scr.ld (show 8 * sArr aAcc + 8 ≤ L.Z by
    have := hdr_lt_slot L.w 8 (show sArr aAcc < 32 by decide); omega)
  unfold AdxRotate8.setupBases
  xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.harr aAcc (by decide), off_add16]

theorem setup_ct : RelCT isa (Two GoodW) (.block AdxRotate8.setup) (fun _ _ => True) := by
  unfold AdxRotate8.setup
  apply VG.RelCT.block_append
  refine RelCT.seq (two_piece [.rdi] pins_goodW (by taint_decide) setupBases_fw) ?_
  exact two_taint [.rcx] (fun L s t hs ht r hr => by
    have he : r = .rcx := List.mem_singleton.mp hr
    subst r; exact hs.trans ht.symm) (by taint_decide)

def EndW (L : Ws) (s : State) : Prop := GoodW L s ∧ s.gpr .rcx = off L.B (slot L.w aTmp)

theorem finish_ct : RelCT isa (Two EndW) (.block AdxRotate8.finish) (fun _ _ => True) := by
  unfold AdxRotate8.finish
  apply VG.RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun L s => s.gpr .r8 = off L.B (slot L.w aTmp) ∧
    s.gpr .rbp = BitVec.ofNat 64 L.w) [.rdi, .rcx] ?_ (by taint_decide) ?_) ?_
  · intro L s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pins_goodW L s t hs.1 ht.1 .rdi (by simp)
    · rw [hs.2, ht.2]
  · intro L s ⟨⟨mi, hg, hZ⟩, hc⟩
    exact WP.mono (finishSetup_ok hg.scr hg.rdi hg.hdr hZ hc) fun _ h => ⟨h.1, h.2.1⟩
  · refine two_taint [.r8, .rbp] ?_ (by taint_decide)
    intro L s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hs.1, ht.1]
    · rw [hs.2, ht.2]
end VG.Proof.Bignum.X86_64.AdxRotate8
