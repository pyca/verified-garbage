module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Stage
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # A context prepared from a cached `R² mod p` (i686)

`vg_rsa_private_crt_precomputed` sets a factor's context up from its
`R_pre² mod p` in `pre`, for `R_pre = 2^(64 w)`, `w = max(2, ⌈l / 8⌉)` and
the factor's length `l`: `primeBytes` computes `8 w` (`primeBytes_ok`);
`loadR2` copies the value into slot 4 and counts the doublings to the
context's radix (`loadR2_ok`); `preparePre` leaves what `prepare` does
(`preparePre_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86.PublicRt (argAt)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `primeBytes r t`: `r = 8 max(2, ⌈l / 8⌉)` from `r = l ≥ 1`. -/
theorem primeBytes_ok {r t : Reg} (hrt : r ≠ t) {l : Nat} (hr : s.gpr r = BitVec.ofNat 32 l) (hl : 1 ≤ l)
    (hl' : l < 2 ^ 31)
    (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem →
      u.gpr r = BitVec.ofNat 32 (8 * Spec.Rsa.primeWords l) → WP isa (.block is) u Q) :
    WP isa (.block (primeBytes r t ++ is)) s Q := by
  simp only [primeBytes, List.cons_append, List.nil_append]
  refine wp_addS rfl fun u₁ U₁ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₂ U₂ => ?_
  refine wp_movS rfl fun u₃ U₃ _ => wp_subS rfl fun u₄ U₄ c₄ => wp_sbbS rfl c₄ fun u₅ U₅ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₆ U₆ => wp_addS rfl fun u₇ U₇ _ => ?_
  refine wp_addS rfl fun u₈ U₈ _ => wp_addS rfl fun u₉ U₉ _ => wp_addS rfl fun u₁₀ U₁₀ _ => ?_
  have K : Keeps [r, t] s u₁₀ := by
    refine ((((U₁.keeps.mono (by simp)).trans (U₂.keeps.mono (by simp))).trans
      ((U₃.keeps.mono (by simp)).trans (U₄.keeps.mono (by simp)))).trans
      (((U₅.keeps.mono (by simp)).trans (U₆.keeps.mono (by simp))).trans
      ((U₇.keeps.mono (by simp)).trans (U₈.keeps.mono (by simp))))).trans
      ((U₉.keeps.mono (by simp)).trans (U₁₀.keeps.mono (by simp)))
  refine kk u₁₀ K (by rw [U₁₀.mem, U₉.mem, U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]) ?_
  -- `x = ⌈l / 8⌉`, and one more if it is one.
  have hx : (u₂.gpr r).toNat = (l + 7) / 8 := by
    rw [U₂.gpr, BitVec.toNat_ushiftRight, U₁.gpr, hr, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (7 : BitVec 32).toNat = 7 from rfl, Nat.shiftRight_eq_div_pow]
    congr 1; omega
  have r₅ : u₅.gpr r = u₂.gpr r := by
    rw [U₅.other _ hrt, U₄.other _ hrt, U₃.other _ hrt]
  have t₆ : (u₆.gpr t).toNat = if (l + 7) / 8 < 2 then 1 else 0 := by
    rw [U₆.gpr, ite_eq_left rfl, U₅.gpr, BitVec.sub_self, BitVec.toNat_and, U₃.gpr, hx]
    by_cases e : (l + 7) / 8 < 2 <;> simp [e]
  have r₇ : (u₇.gpr r).toNat = (l + 7) / 8 + (if (l + 7) / 8 < 2 then 1 else 0) := by
    rw [U₇.gpr, BitVec.toNat_add, t₆, U₆.other _ hrt, r₅, hx]
    split <;> omega
  apply BitVec.eq_of_toNat_eq
  rw [U₁₀.gpr, U₉.gpr, U₈.gpr]
  simp only [BitVec.toNat_add, r₇, BitVec.toNat_ofNat, Spec.Rsa.primeWords, Spec.Rsa.modulusWords]
  split <;> omega

end

end VG.Proof.Bignum.X86.CrtRt
