import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lanes
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame

/-! ## From `MontProductVec.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes)
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)

def result (a b : Nat) : Nat := mont (a*b) % q

/-- The selected seven-instruction REDC and two-instruction canonical correction. -/
theorem arithmetic_ok {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B)
    (halt : ∀ e < 4, A e < 3*q) (hblt : ∀ e < 4, B e < 3*q)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v2,.v3,.v4,.v0] s t →
      Lanes (t.v .v0) (fun e => result (A e) (B e)) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.MontProduct.arithmetic ++ rest)) s Q := by
  change WP isa (.block (VG.Impl.MlDsa.AArch64.Arith.Neon.mont .v0 .v1 ++
    (VG.Impl.MlDsa.AArch64.Arith.Neon.csub .v0 .v4 ++ rest))) s Q
  refine mont_ok (by decide) (by decide) hc.q hc.qi fun t ht hv => ?_
  have hl : Lanes (t.v .v0) (fun e => mont (A e * B e)) := by
    intro e he
    rw [hv, VG.Proof.MlKem.AArch64.vword_ofVWords _ _ _ _ he]
    have hm (i : Nat) (hi : i<4) :
        (redc (product (vword (s.v .v0) i) (vword (s.v .v1) i))).toNat = mont (A i*B i) := by
      rw [lazy_mont_word_nat _ _ (by rw [ha i hi]; exact halt i hi)
        (by rw [hb i hi]; exact hblt i hi),ha i hi,hb i hi]
    rcases (show e=0 ∨ e=1 ∨ e=2 ∨ e=3 by omega) with rfl | rfl | rfl | rfl <;>
      exact hm _ (by decide)
  refine csub_ok (by decide) (hc.chg ht).lanes_q hl
    (fun e he => mont_lt (product_lt_qR (halt e he) (hblt e he))) fun u hu hlu =>
      k u (ht.trans hu).mono hlu
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end

/-! ## From `MontProductMem.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MontProduct
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_ldrq wp_strq)
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Spec.MlDsa (q)
/-- Two vector loads, the canonical arithmetic, and one vector store. -/
theorem group_ok {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.mem.read (s.gpr .x1) 16) A)
    (hb : Lanes (s.mem.read (s.gpr .x2) 16) B)
    (halt : ∀ e < 4, A e < 3*q) (hblt : ∀ e < 4, B e < 3*q)
    (hra : InRegions (s.rd++s.wr) (s.gpr .x1) 16)
    (hrb : InRegions (s.rd++s.wr) (s.gpr .x2) 16)
    (hw : InRegions s.wr (s.gpr .x0) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t v, StepKeep [.v0,.v1,.v2,.v3,.v4] s t →
      t.mem = s.mem.write (s.gpr .x0) 16 v →
      Lanes v (fun e => result (A e) (B e)) → WP isa (.block rest) t Q) :
    WP isa (.block (([.ldrq .v0 .x1 0,.ldrq .v1 .x2 0] : List Instr) ++
      VG.Impl.MlDsa.AArch64.Optimized.MontProduct.arithmetic ++ ([.strq .v0 .x0 0] : List Instr) ++ rest)) s Q := by
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq (by decide) rfl (by simpa using hra) fun a h1 => ?_
  refine wp_ldrq (by decide) rfl (by simpa only [h1.chg.rd,h1.chg.wr,h1.chg.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hrb) fun b h2 => ?_
  have hk : VChg [.v0,.v1] s b := (h1.chg.trans h2.chg).mono (by decide)
  have hA : Lanes (b.v .v0) A := by
    rw [h2.get .v0,h1.v]; simpa using ha
  have hB : Lanes (b.v .v1) B := by
    rw [h2.v,h1.chg.mem,h1.chg.gpr]; simpa using hb
  refine arithmetic_ok (hc.chg hk) hA hB halt hblt fun c h3 hval => ?_
  have hk' : VChg [.v0,.v1,.v2,.v3,.v4] s c := (hk.trans h3).mono (by decide)
  refine wp_strq (by decide) rfl (by simpa only [hk'.wr,hk'.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw) fun d h4 => ?_
  refine k d (c.v .v0) ?_ ?_ hval
  · exact ((StepKeep.ofChg hk' (by decide)).trans (StepKeep.ofMem h4)).mono (by decide)
  · simp only [h4.mem,hk'.mem,hk'.gpr,BitVec.add_zero]

theorem body_ok {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.mem.read (s.gpr .x1) 16) A)
    (hb : Lanes (s.mem.read (s.gpr .x2) 16) B)
    (halt : ∀ e < 4, A e < 3*q) (hblt : ∀ e < 4, B e < 3*q)
    (hra : InRegions (s.rd++s.wr) (s.gpr .x1) 16)
    (hrb : InRegions (s.rd++s.wr) (s.gpr .x2) 16)
    (hw : InRegions s.wr (s.gpr .x0) 16) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.MontProduct.body)) s fun t =>
      ∃ v, t.mem = s.mem.write (s.gpr .x0) 16 v ∧
        Lanes v (fun e => result (A e) (B e)) ∧ VConsts t ∧
        t.gpr .x0 = s.gpr .x0 + 16 ∧ t.gpr .x1 = s.gpr .x1 + 16 ∧ t.gpr .x2 = s.gpr .x2 + 16 ∧
        t.gpr .x12 = s.gpr .x12 - 1 ∧ VG.Proof.MlKem.AArch64.Keep [.x0,.x1,.x2,.x12] s t := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.MontProduct.body
  have he : ([Instr.strq .v0 .x0 0, .addImm .x .x0 .x0 16,
      .addImm .x .x1 .x1 16,.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1] : List Instr) =
      [.strq .v0 .x0 0] ++ [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,.addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1] := rfl
  rw [he, ← List.append_assoc]
  refine group_ok hc ha hb halt hblt hra hrb hw fun t v hk hm hl => ?_
  have ct : VConsts t := ⟨by rw [hk.vec .v16 (by decide)]; exact hc.q,
    by rw [hk.vec .v17 (by decide)]; exact hc.qi⟩
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,.addImm .x .x2 .x2 16,
      .subImm .x .x12 .x12 1]) t fun u =>
      u.mem=t.mem ∧ u.v=t.v ∧ u.gpr .x0=t.gpr .x0+16 ∧
      u.gpr .x1=t.gpr .x1+16 ∧ u.gpr .x2=t.gpr .x2+16 ∧ u.gpr .x12=t.gpr .x12-1 := by
    arun [State.write, BitVec.ofNat_eq_ofNat]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x0,.x1,.x2,.x12] scalar (by decide))
    fun u ⟨⟨hum,huv,h0,h1,h2,h12⟩,ku⟩ => ?_
  refine ⟨v, hum.trans hm, hl, ?_, ?_, ?_, ?_, ?_, (hk.keep.trans ku).mono⟩
  · exact ⟨by rw [huv]; exact ct.q, by rw [huv]; exact ct.qi⟩
  · simpa only [hk.keep.get .x0] using h0
  · simpa only [hk.keep.get .x1] using h1
  · simpa only [hk.keep.get .x2] using h2
  · simpa only [hk.keep.get .x12] using h12
end VG.Proof.MlDsa.AArch64.Optimized.MontProduct

end
