module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Linear
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Shr
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Reduce
import VerifiedGarbage.Proof.Divstep.Tc32Words
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Abs

/-! # The matrix rows of a batch at a run-time width

`fgRow_ok`: a row of the full-width values, `[a j] = (u f + v g) / 2 ^ 30` (`InvBatch.fgRow_ok`);
`abRow_ok`: a row of the coefficients, `[a j] = mred p iv (u a + v b)` (`InvBatch.abRow_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem rv_a (len j : Nat) : rv (kw len) (a j) = 160 + j * (8 * nw len + 8) := by
  have := rv_arr (kw len) j 0
  have ke := kw_eq len
  rw [show 4 * kw len + 8 = 8 * nw len + 8 by omega] at this
  simp only [a]; omega

/-- The arrays fit: `[16]` begins inside the working space. -/
theorem Bx.fits16 {s : State} (h : Bx L s B Z len N) : 160 + 16 * (8 * nw len + 8) ≤ Z := by
  have := h.fits
  have ke := kw_eq len
  simp only [VG.Impl.Rsa.X86.InvBatch.offset] at this
  omega

/-- A matrix row of the full-width values: `[a j] = (u f + v g) / 2 ^ 30`, `n + 1` words. -/
theorem fgRow_ok {s : State} (h : Bx L s B Z len N) (he : nw len % 2 = 0) {u v j : Nat}
    (hu4 : u + 4 ≤ 160) (hv4 : v + 4 ≤ 160) (hj : j < 2) {cu cv f g : Int} {p : Nat}
    (hu : s.mem.readW (off B u) 32 = BitVec.ofInt 32 cu) (hv : s.mem.readW (off B v) 32 = BitVec.ofInt 32 cv)
    (huv : |cu| + |cv| ≤ 2 ^ 30)
    (hf : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      f % 2 ^ (32 * (nw len + 1)))
    (hg : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      g % 2 ^ (32 * (nw len + 1)))
    (hfb : |f| ≤ p) (hgb : |g| ≤ p) (hp : p < 2 ^ (32 * nw len + 1)) (hdiv : 2 ^ 30 ∣ cu * f + cv * g) :
    WP isa (.seq (linear L u v (a 11) (a 4) (a 5) (a 12) 1) (shr30 L (a j) (a 11))) s fun z =>
      Bx L z B Z len N ∧
      (val32 z.mem B (rv (kw len) (a j)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
        ((cu * f + cv * g) / 2 ^ 30) % 2 ^ (32 * (nw len + 1)) ∧
      Keeps wordClob s z ∧
      Unch B [(rv (kw len) (a 11), 4 * (nw len + 3)), (rv (kw len) (a 12), 4 * nw len),
        (rv (kw len) (a j), 4 * (nw len + 1))] s.mem z.mem := by
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have r4 := rv_a len 4; have r5 := rv_a len 5; have r11 := rv_a len 11; have r12 := rv_a len 12
  have rj := rv_a len j
  have hjb := Nat.mul_le_mul_right (8 * nw len + 8) (show j ≤ 1 by omega)
  rw [Nat.one_mul] at hjb
  refine WP.seq (WP.mono (linear_ok h (e := 1) (tmp := a 12) hu4 hv4 (by decide) rfl rfl rfl
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun s₁ ⟨H₁, U₁, K₁, V₁⟩ => ?_)
  rw [hu, hv, Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
    Divstep.W32.toInt_small (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv),
    Divstep.W32.cong_comb hf hg] at V₁
  have hcomb := Divstep.W32.comb_le huv hfb hgb
  have hpI : (p : Int) < 2 ^ (32 * nw len) * 2 := by
    exact_mod_cast (by simpa only [Nat.pow_succ] using hp)
  have cap : ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) = (2 : Int) ^ (32 * nw len) * 2 ^ 31 := by
    push_cast; rfl
  have lo : -((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) ≤ cu * f + cv * g := by
    rw [cap]; have := neg_abs_le (cu * f + cv * g); linarith
  have hi : cu * f + cv * g < ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) := by
    rw [cap]; have := le_abs_self (cu * f + cv * g); linarith
  refine WP.mono (shrSigned_ok H₁ (dst := a j) (src := a 11) rfl he (by omega) (by omega) (by omega)
    (by exact_mod_cast V₁) lo hi (Int.mul_ediv_cancel' hdiv).symm)
    fun z ⟨Hz, V, K, O⟩ => ⟨Hz, by exact_mod_cast V, (K₁.mono (by decide)).trans (K.mono (by decide)), ?_⟩
  intro x hx
  rw [O x (hx (rv (kw len) (a j), 4 * (nw len + 1)) (by simp)), U₁ x (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hx (rv (kw len) (a 11), 4 * (nw len + 3)) (by simp)
    · exact hx (rv (kw len) (a 12), 4 * nw len) (by simp))]

end VG.Proof.Rsa.X86.InvBatchRt
