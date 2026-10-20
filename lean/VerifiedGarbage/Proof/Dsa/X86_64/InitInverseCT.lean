module

public import VerifiedGarbage.Proof.Dsa.X86_64.InitInverse
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.InitInverse
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time Montgomery inverse initialization -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem initInverse_ct : RelCT isa (Two GoodW) (.block initInverse) (fun _ _ => True) := by
  change RelCT isa (Two GoodW) (.block (([.mov .rbx (.mem (hdr (sArr aN)))] : List Instr) ++
    ([.mov .rbx (.mem (at0 .rbx))] ++ minv ++ [.store (hdr sMinv) .r15]))) (fun _ _ => True)
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun (L : Ws) t =>
    t.gpr .rdi = L.B ∧ t.gpr .rbx = off L.B (slot L.w aN)) [.rdi] pins_goodW (by taint_decide) ?_) ?_
  · intro L s ⟨_, hg⟩
    refine WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = off L.B (slot L.w aN)) ?_ rfl)
      fun t ⟨hb, hk⟩ => ⟨(hk.gpr (by decide)).trans hg.1.rdi, hb⟩
    xrun [State.ea, hdr, hdrOff, hg.1.rdi, hg.1.hdr.harr aN (by decide),
      hg.1.scr.ld (Nat.le_trans (hdr_lt_slot L.w 8 (show sArr aN < 32 by decide)) hg.2)]
  · exact two_taint [.rdi, .rbx]
      (pins_of (fun L r => if r = .rdi then L.B else off L.B (slot L.w aN)) (by
        intro L s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2)) (by taint_decide)

end VG.Proof.Dsa.X86_64
