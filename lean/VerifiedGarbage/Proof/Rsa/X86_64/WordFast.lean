module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
public import VerifiedGarbage.Proof.Rsa.X86_64.WordNormalize
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep

/-! # A normalized computation even when the output mask rejects the factors -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordDivide

open VG VG.X86_64 VG.Impl.Rsa.X86_64.WordDivide
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Normalization writes only the divisor array in addition to the reducer's ranges. -/
def normRanges (W : Nat) : List (Nat × Nat) := (slot W aM, 8 * (W + 2)) :: allRanges W

theorem fast_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W)
    (hZ : slot W 17 ≤ Z) (hW : 4 ≤ W) :
    WP isa (.seq (.block normalize) code) s fun t =>
      (2 ^ 63 ≤ (word s.mem B (slot W aM + 8 * (W / 2 - 1))).toNat →
        wv t.mem B (slot W aR) (W + 1) =
          wv s.mem B (slot W aD) W % wv s.mem B (slot W aM) (W / 2)) ∧
      Frm B (normRanges W) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have hM := h.sl (j := aM) (by decide)
  have hD := h.sl (j := aD) (by decide)
  have hw := h.w2
  refine WP.seq (WP.mono (normalize_ok h hW) fun s₁ ⟨m₁, k₁⟩ => ?_)
  have o₁ : Outside B (slot W aM + 8 * (W / 2 - 1)) 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by omega_arith)
  have f₁ : Frm B (normRanges W) s.mem s₁.mem := by
    apply cover (Frm.of_outside o₁ (by simp : (slot W aM + 8 * (W / 2 - 1), 8) ∈
      [(slot W aM + 8 * (W / 2 - 1), 8)]))
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    exact ⟨(slot W aM, 8 * (W + 2)), by simp [normRanges], by omega_arith, by omega_arith⟩
  have h₁ := h.congr f₁ (fun r hr => by
    simp only [normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact Mut.ofSlot _ _ _
    · exact all_mut hr) k₁ (by decide)
  have top : 2 ^ 63 ≤ (word s₁.mem B (slot W aM + 8 * (W / 2 - 1))).toNat := by
    rw [m₁, word_writeW_self]; exact high_or _
  refine WP.mono (code_ok h₁ hZ hW top (modulus_pos (by omega_arith) top)) fun t ⟨v, ff, kk⟩ => ?_
  refine ⟨fun hd => ?_, f₁.trans (ff.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)),
    (k₁.trans kk).mono (by simp)⟩
  rw [v, o₁.wv (by simp only [slot, aD, aM]; omega_arith) (by omega_arith)]
  congr 1
  rw [m₁, high_or_self _ hd]
  have npos : 1 ≤ W / 2 := by omega_using [hW]
  have he : W / 2 = (W / 2 - 1) + 1 := by omega_using [npos]
  conv => lhs; arg 4; rw [he]
  rw [wv_writeW_top _ _ _ _ _ (by omega_arith)]
  symm
  rw [he, wv]
  simp only [Nat.add_sub_cancel]

/-- A numerical high-bit bound implies the word kernel's normalization premise. -/
theorem top_of_bound {m : Mem} {B : Addr} {e n : Nat} (hn : 1 ≤ n)
    (hb : 2 ^ (64 * n - 1) ≤ wv m B e n) : 2 ^ 63 ≤ (word m B (e + 8 * (n - 1))).toNat := by
  apply (R2w.top_half m B e (n - 1)).mp
  rw [show n - 1 + 1 = n by omega_using [hn]]
  have he : 2 ^ (64 * n) / 2 = 2 ^ (64 * n - 1) := by
    rw [show 64 * n = (64 * n - 1) + 1 by omega_using [hn], Nat.pow_succ,
      Nat.mul_div_cancel _ (by decide)]
    simp only [Nat.add_sub_cancel]
  rwa [he]

end VG.Proof.Rsa.X86_64.WordDivide
