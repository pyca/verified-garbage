import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lane0
import VerifiedGarbage.Proof.Framework.X86_64.YFrame

/-!
# The eight-block loop's carry-less products and reduction

The first product initializes the accumulators. Reduction folds `lo` into
`mid` and then `mid` into `hi`, using the same `reduceB` as the AVX-512
implementation, on a single 128-bit lane.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.X86_64.RegUpd
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod Only reduceB eval_pxor)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchAvx8 (accInit acc reduceFinal)

private theorem xmm_setXmm (s : State) (d r : XReg) (v : BitVec 128) :
    (s.setXmm d v).xmm r = if r = d then v else s.xmm r := rfl

private theorem liftPure (is ss : List Instr) (rs : List XReg)
    (hcode : lane0Block is = some ss) (hgp : is.all noGpr = true)
    (hdst : ∀ r, r ∉ rs → r ∉ is.filterMap vdst)
    (post : State → Prop) (s : State)
    (h : WP isa (.block ss) (s.proj 0) fun t => post t ∧ Only rs (s.proj 0) t) :
    WP isa (.block is) s fun s' => post (s'.proj 0) ∧ YFrame rs s s' := by
  refine WP.mono (WP.lane0 hcode h) fun s' ⟨⟨hp, ho⟩, hi, hg⟩ => ?_
  refine ⟨hp, hg hgp, by simpa using ho.mem, by simpa using ho.rd,
    by simpa using ho.wr, fun r hr l hl => ?_⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simpa using ho.xmm r hr
  · exact hi r (hdst r hr)

private def initSse : List Instr :=
  [.xop (.bin .movdqa .xmm8 .xmm7), .xop (.pclmulqdq .xmm8 .xmm12 0x00),
   .xop (.bin .movdqa .xmm10 .xmm7), .xop (.pclmulqdq .xmm10 .xmm12 0x11),
   .xop (.bin .movdqa .xmm9 .xmm7), .xop (.pclmulqdq .xmm9 .xmm12 0x01),
   .xop (.bin .movdqa .xmm11 .xmm7), .xop (.pclmulqdq .xmm11 .xmm12 0x10),
   .xop (.bin .pxor .xmm9 .xmm11)]

private theorem initSse_ok (s : State) :
    WP isa (.block initSse) s fun s' =>
      prod s' = Prod.zero.acc (s.xmm .xmm7) (s.xmm .xmm12) ∧
      Only [.xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  apply WP.of_runBlock
  simp only [initSse, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, eval_pxor, eval_movdqa, xmm_setXmm, reduceCtorEq, ↓reduceIte,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [prod, Prod.acc, Prod.zero, xmm_setXmm]
  · intro r hr; simp only [gpr_setXmm]
  · simp only [mem_setXmm]
  · simp only [rd_setXmm]
  · simp only [wr_setXmm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem accInit_ok (s : State) :
    WP isa (.block (accInit .xmm7 .xmm12)) s fun s' =>
      prod (s'.proj 0) = Prod.zero.acc (s.lane .xmm7 0) (s.lane .xmm12 0) ∧
      YFrame [.xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  refine liftPure _ initSse _ rfl rfl ?_ _ s (initSse_ok (s.proj 0))
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [accInit, vdst, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

theorem acc_ok (s : State) :
    WP isa (.block (acc .xmm7 .xmm12)) s fun s' =>
      prod (s'.proj 0) = (prod (s.proj 0)).acc (s.lane .xmm7 0) (s.lane .xmm12 0) ∧
      YFrame [.xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  refine liftPure _ (Impl.Gcm.X86_64.Pclmul.acc .xmm7 .xmm12) _ rfl rfl ?_ _ s
    (Pclmul.acc_ok .xmm7 .xmm12 (s.proj 0) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [acc, vdst, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

private def redSse : List Instr :=
  [.movdquLoad .xmm1 (at_ .r11 784),
   .xop (.bin .movdqa .xmm11 .xmm8), .xop (.pclmulqdq .xmm11 .xmm1 0x10),
   .xop (.pshufd .xmm8 .xmm8 0x4e),
   .xop (.bin .pxor .xmm9 .xmm8), .xop (.bin .pxor .xmm9 .xmm11),
   .xop (.bin .movdqa .xmm11 .xmm9), .xop (.pclmulqdq .xmm11 .xmm1 0x10),
   .xop (.pshufd .xmm9 .xmm9 0x4e),
   .xop (.bin .movdqa .xmm2 .xmm10), .xop (.bin .pxor .xmm2 .xmm9),
   .xop (.bin .pxor .xmm2 .xmm11)]

private theorem redSse_ok (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 784)) 16)
    (hc : s.mem.readW (s.ea (at_ .r11 784)) 128 = poly) :
    WP isa (.block redSse) s fun s' =>
      s'.xmm .xmm2 = reduceB (prod s) ∧ Only [.xmm1, .xmm2, .xmm8, .xmm9, .xmm11] s s' := by
  apply WP.of_runBlock
  simp only [redSse, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.load128, hin, Option.map_some, eval_pxor, eval_movdqa,
    xmm_setXmm, reduceCtorEq, ↓reduceIte, hc, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [reduceB, Pclmul.fold, prod, BitVec.xor_assoc]
  · intro r hr; simp only [gpr_setXmm]
  · simp only [mem_setXmm]
  · simp only [rd_setXmm]
  · simp only [wr_setXmm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [xmm_setXmm, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem reduceFinal_ok (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ .r11 784)) 16)
    (hc : s.mem.readW (s.ea (at_ .r11 784)) 128 = poly) :
    WP isa (.block reduceFinal) s fun s' =>
      s'.lane .xmm2 0 = reduceB (prod (s.proj 0)) ∧
      YFrame [.xmm1, .xmm2, .xmm8, .xmm9, .xmm11] s s' := by
  refine liftPure _ redSse _ rfl rfl ?_ _ s (redSse_ok (s.proj 0) hin hc)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [reduceFinal, vdst, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]

end VG.Proof.Gcm.X86_64.StitchAvx8
