import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Proof.Ed25519.X86.CombLit
import VerifiedGarbage.Proof.Ed25519.X86.CallTaint

/-! The comb has a public trace: its loops' counters (`esi`) are public, and every address is
the workspace pointer `edi` plus a constant or `8 esi`, or the tables' address plus
`768 esi` and a constant. The tables' address is the word at byte `combTbl` of the workspace,
which the comb never writes, public: the digits only reach masks. The field products are calls
of `vg_gf25519_r32_mul`, so the comb is related run by run (`AR`), with `edi`, `esi` and that
word public across the calls. -/
namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86

/-- What the comb needs public: `edi` and the tables' address. -/
abbrev τC : VG.X86.Taint.T := ptR [.edi] [combTbl]

/-- ... and its counter `esi`. -/
abbrev τCS : VG.X86.Taint.T := ptR [.edi, .esi] [combTbl]

theorem combMultiply_ar (x : BitVec 32) : RelCT isa (AR x τC) combMultiply (AR x τCS) := by
  have hb := ptR_base [.edi, .esi] [combTbl]
  have step : RelCT isa (AR x τCS) combStep fun s t => isa.eval .ne s = isa.eval .ne t ∧ AR x τCS s t :=
    (block_to x (by decide +kernel) hb).seq <| (block_to x (by decide +kernel) hb).seq <|
      (block_to x (by decide +kernel) hb).seq <|
      (fieldProg_ar x (by decide +kernel) hb addOddOps (by decide +kernel)).seq <|
      (block_to x (by decide +kernel) hb).seq <|
      (fieldProg_ar x (by decide +kernel) hb addEvenOps (by decide +kernel)).seq <|
      block_cond x .ne (by decide +kernel) hb
  have dbl : RelCT isa (AR x τCS) doubleBody fun s t => isa.eval .ne s = isa.eval .ne t ∧ AR x τCS s t :=
    (fieldProg_ar x (by decide +kernel) hb pointDoubleOps (by decide +kernel)).seq
      (block_cond x .ne (by decide +kernel) hb)
  have finish : RelCT isa (AR x τCS) combFinish (AR x τCS) :=
    ((block_to x (by decide +kernel) hb).seq (loop_inv dbl)).seq <|
      (block_to x (by decide +kernel) hb).seq
        (fieldProg_ar x (by decide +kernel) hb pointAddOps (by decide +kernel))
  exact (block_to x (τ := τC) (σ := τCS) (by decide +kernel) hb).seq ((loop_inv step).seq finish)

theorem combMultiply_ct {x : BitVec 32} : RelCT isa
    (fun s t => PointCTCtx x s ∧ PointCTCtx x t ∧ s.wr = t.wr ∧ s.gpr .esp = t.gpr .esp ∧
      wd s.mem x combTbl = wd t.mem x combTbl) combMultiply (fun _ _ => True) :=
  (combMultiply_ar x).mono
    (fun _ _ h => ⟨ptR_agree h.1 h.2.1 h.2.2.1 (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact h.1.ctx.edi.trans h.2.1.ctx.edi.symm)
        (fun o ho => by rw [List.mem_singleton.mp ho]; exact ⟨by decide, h.2.2.2.2⟩),
      h.1, h.2.1, h.2.2.2.1⟩)
    fun _ _ _ => trivial

end VG.Proof.Ed25519.X86
