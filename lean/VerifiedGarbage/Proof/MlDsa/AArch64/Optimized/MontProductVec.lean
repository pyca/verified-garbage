import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lanes

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
