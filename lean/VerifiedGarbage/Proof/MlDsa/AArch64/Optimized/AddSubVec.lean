import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.AddSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lanes

namespace VG.Proof.MlDsa.AArch64.Optimized.AddSub
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_vop lanes_add lanes_sub)
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Spec.MlDsa (q)

/-- Exact measured vector addition, including unsigned conditional reduction. -/
theorem add_ok {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v0,.v4] s t →
      Lanes (t.v .v0) (fun e => (A e + B e) % q) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic false ++ rest)) s Q := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic, Bool.false_eq_true,
    ↓reduceIte, List.cons_append, List.nil_append]
  refine wp_vop (d := .v0) rfl fun t ht => ?_
  have hsum : Lanes (t.v .v0) (fun e => A e + B e) := by
    rw [ht.v]
    exact (lanes_add ha hb).congr fun e he => Nat.mod_eq_of_lt (by
      have := halt e he; have := hblt e he; simp only [VG.Spec.MlDsa.q] at *; omega)
  refine csub_ok (by decide) (hc.chg ht.chg).lanes_q hsum
    (fun e he => by have := halt e he; have := hblt e he; omega) fun u hu hv =>
      k u (ht.chg.trans hu).mono hv

/-- Exact measured vector subtraction, with q added before the subtraction. -/
theorem sub_ok {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v0,.v4] s t →
      Lanes (t.v .v0) (fun e => (A e + q - B e) % q) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic true ++ rest)) s Q := by
  simp only [VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic, ↓reduceIte,
    List.cons_append, List.nil_append]
  refine wp_vop (d := .v0) rfl fun t ht => wp_vop (d := .v0) rfl fun u hu => ?_
  have hsum : Lanes (t.v .v0) (fun e => A e + q) := by
    rw [ht.v]
    exact (lanes_add ha hc.lanes_q).congr fun e he => Nat.mod_eq_of_lt (by
      have := halt e he; change A e < 8380417 at this
      change A e + 8380417 < 2^32; omega)
  have hb' : Lanes (t.v .v1) B := by rw [ht.get .v1]; exact hb
  have hdiff : Lanes (u.v .v0) (fun e => A e + q - B e) := by
    rw [hu.v]
    exact (lanes_sub hsum hb').congr fun e he => by
      have := halt e he; have := hblt e he
      simp only [VG.Spec.MlDsa.q] at *
      omega
  refine csub_ok (by decide) (hc.chg (ht.chg.trans hu.chg)).lanes_q hdiff
    (fun e he => by have := halt e he; have := hblt e he; omega) fun v hv hl =>
      k v ((ht.chg.trans hu.chg).trans hv).mono hl
end VG.Proof.MlDsa.AArch64.Optimized.AddSub
