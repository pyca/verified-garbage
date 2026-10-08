import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lane0
import VerifiedGarbage.Proof.Framework.X86_64.YFrame

/-!
# Folding the three GHASH product words directly

The AVX-512 path's reduction also works on a single 128-bit lane. It folds
`lo` into `mid`, then `mid` into `hi`, saving three vector instructions.
The field interpretation is established when the loop is connected to GHASH
in `Ok.lean`, keeping the algebra out of the instruction proofs.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only reduceB eval_pxor)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchAvx (reduceHash)

private theorem xmm_setXmm (s : State) (d r : XReg) (v : BitVec 128) :
    (s.setXmm d v).xmm r = if r = d then v else s.xmm r := rfl

private def redSse : List Instr :=
  [.xop (.bin .movdqa .xmm11 .xmm8), .xop (.pclmulqdq .xmm11 .xmm1 0x10),
   .xop (.pshufd .xmm8 .xmm8 0x4e),
   .xop (.bin .pxor .xmm9 .xmm8), .xop (.bin .pxor .xmm9 .xmm11),
   .xop (.bin .movdqa .xmm11 .xmm9), .xop (.pclmulqdq .xmm11 .xmm1 0x10),
   .xop (.pshufd .xmm9 .xmm9 0x4e),
   .xop (.bin .movdqa .xmm2 .xmm10), .xop (.bin .pxor .xmm2 .xmm9),
   .xop (.bin .pxor .xmm2 .xmm11)]

private theorem redSse_ok (s : State) (hc : s.xmm .xmm1 = poly) :
    WP isa (.block redSse) s fun t =>
      t.xmm .xmm2 = reduceB (prod s) ∧ Only [.xmm8, .xmm9, .xmm10, .xmm11, .xmm2] s t := by
  apply WP.of_runBlock
  simp only [redSse, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, eval_pxor, eval_movdqa, xmm_setXmm, reduceCtorEq, ↓reduceIte,
    hc, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [reduceB, Pclmul.fold, prod, BitVec.xor_assoc]
  · intro r hr; simp only [gpr_setXmm]
  · simp only [mem_setXmm]
  · simp only [rd_setXmm]
  · simp only [wr_setXmm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem reduceHash_ok (s : State) (h1 : s.lane .xmm1 0 = poly) :
    WP isa (.block reduceHash) s fun t =>
      t.lane .xmm2 0 = reduceB (prod (s.proj 0)) ∧
      YFrame [.xmm8, .xmm9, .xmm10, .xmm11, .xmm2] s t := by
  refine WP.mono (WP.lane0 (ss := redSse) rfl (redSse_ok (s.proj 0) h1))
    fun t ⟨⟨hv, ho⟩, hi, hg⟩ => ⟨hv, ?_⟩
  refine ⟨hg rfl, ho.mem, ho.rd, ho.wr, fun r hr l hl => ?_⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact ho.xmm r hr
  · apply hi r
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [reduceHash, vdst, hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2]

end VG.Proof.Gcm.X86_64.StitchAvx
