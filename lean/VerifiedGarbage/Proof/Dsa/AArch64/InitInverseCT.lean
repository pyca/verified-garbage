module

public import VerifiedGarbage.Proof.Dsa.AArch64.InitInverse
meta import VerifiedGarbage.Proof.Dsa.AArch64.InitInverse
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant-time Montgomery inverse initialization -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem initInverse_ct : RelCT isa (Two GoodW) (.block initInverse) (fun _ _ => True) := by
  change RelCT isa (Two GoodW) (.block (([ldh .x3 (sArr aN)] : List Instr) ++
    ([ld .x3 .x3] ++ minv ++ [sth .x15 sMinv]))) (fun _ _ => True)
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun (L : Ws) t =>
    t.gpr .x0 = L.B ∧ t.gpr .x3 = off L.B (slot L.w aN)) [.x0] pins_goodW (by taint_decide) ?_) ?_
  · intro L s ⟨_, hg⟩
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = off L.B (slot L.w aN)) ?_ (by decide) (by decide)
      (by decide +kernel))
      fun t ⟨hb, hk⟩ => ⟨(hk.gpr .x0 (by decide)).trans hg.1.x0, hb⟩
    brun [hg.1.x0, hdr_enc (show sArr aN < 32 by decide), hg.1.hdr.harr aN (by decide),
      hg.1.scr.ld (Nat.le_trans (hdr_lt_slot L.w 8 (show sArr aN < 32 by decide)) hg.2)]
  · exact two_taint [.x0, .x3]
      (pins_of (fun L r => if r = .x0 then L.B else off L.B (slot L.w aN)) (by
        intro L s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64
