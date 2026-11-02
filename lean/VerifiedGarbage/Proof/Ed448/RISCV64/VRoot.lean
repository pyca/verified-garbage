module

public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Invert
public import VerifiedGarbage.Proof.X25519.RISCV64.Field

/-!
# Ed448 on RISCV64: the square root's power

`root` computes `z^((p-3)/4)` into `R` for the element `z` at `Z2`
(`rootQ_ok`) by X448's addition chain for the inversion as far as
`z^(2²²³ - 1)` (`R64.chain223_ok`), then 223 squarings and the product with
`z^(2²²² - 1)`, since `(p-3)/4 = (2²²³ - 1) 2²²³ + (2²²² - 1)` (`root_exp`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Impl.X448.RISCV64 (R Z2)
open VG.Impl.X448.RISCV64.R64 (T6)
open VG.Spec.X448 (P Fe)

/-- The exponent `(p - 3) / 4`. -/
def RE : Nat := (P - 3) / 4

/-- `(p - 3) / 4 = (2²²³ - 1) 2²²³ + (2²²² - 1)`. -/
theorem root_exp : (2 ^ 223 - 1) * 2 ^ 223 + (2 ^ 222 - 1) = RE := by decide +kernel

section
variable {b : Addr}

theorem rootQ_ok {qs : List Nat} (hq : R64.Sep8 R qs = true) (hZ : Z2 ∈ qs)
    (hT : R64.TempsOk qs = true) {a : BitVec 64} {v : Nat → Fe} {s : State} (hc : Ctx b s)
    (hS : ∀ q ∈ qs, q ≠ R → FS s.mem b q = v q) (h0 : s.gpr .t2 = a) :
    WP isa root s fun s' => R64.Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b qs (upd v R (VG.Proof.X448.pw (v Z2) RE)) := by
  have hZR : Z2 ≠ R := by decide
  obtain ⟨hfR, hfT, hC⟩ := R64.drop_R hq hT hc hS h0
  have hZf : Z2 ∈ qs.filter (· ≠ R) := by simp [hZ, hZR]
  unfold root
  refine WP.seq (WP.mono (R64.chain223_ok hfR hZf hfT hC) fun s1 h1 => ?_)
  obtain ⟨f6, _⟩ := R64.temps_get hfT (t := T6) (by decide)
  refine WP.seq (WP.mono (R64.sqnP (z := v Z2) (ea := 2 ^ 223 - 1) (by decide) (by decide) (by sep8)
    (by decide) (by simp) (by look) h1) fun s2 h2 => ?_)
  refine WP.mono (R64.opMulP (z := v Z2) (ea := (2 ^ 223 - 1) * 2 ^ 223) (eb := 2 ^ 222 - 1) (ee := RE)
    (by sep8) (by decide) (by simp) (by simp) (by look) (by look) root_exp h2) fun s3 ⟨c3, h3⟩ =>
    ⟨h3.stp, h3.ctx, fun q hq' => ?_⟩
  by_cases eR : q = R
  · subst eR
    rw [h3.slots _ List.mem_cons_self, upd_self, upd_self]
  · have hq'' : q ∈ qs.filter (· ≠ R) := by simp [hq', eR]
    have e6 : q ≠ T6 := fun e => (R64.temps_get hT (t := T6) (by decide)).2 (e ▸ hq')
    rw [h3.slots q (by repeat (first | exact hq'' | apply List.mem_cons_of_mem)), upd_of_ne _ _ eR]
    simp only [R64.chainV, upd_of_ne _ _ e6, upd_of_ne _ _ eR]

end

end VG.Proof.Ed448.RISCV64
