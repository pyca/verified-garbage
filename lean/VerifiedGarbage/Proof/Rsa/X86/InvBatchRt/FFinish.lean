module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FStep
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.FScatter
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Red
import VerifiedGarbage.Proof.Rsa.Divstep.Absolute
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: builds in parallel with the batches' (`FBatchStep` to `FInit`)
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The fused batches on i686: the end

`finishF_ok`: from `f`, `d` at byte 8 of the elements (after an odd number of batches) and `p` in
`[2]`: `[1] = |f|` and `[3] = (±d) mod p`, the sign `f`'s.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.F

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob)
open VG.Proof.Rsa.X86.InvBatchRt

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-! ## Two's complement numbers of `n + 1` words -/

/-- `w` holds `x` in two's complement, with `M = 2^(32 n + 31)`. -/
def Rep (M w : Nat) (x : Int) : Prop := w < 2 * M ∧ (w : Int) % (2 * M) = x % (2 * M) ∧ -(M : Int) ≤ x ∧ x < M

theorem Rep.sign {M w : Nat} {x : Int} (h : Rep M w x) : M ≤ w ↔ x < 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hM : (0 : Int) < 2 * M := by omega_using [h0]
  rcases Int.lt_or_le x 0 with hx | hx
  · have : x % (2 * M) = x + 2 * M := by
      rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega_using [h2]) (by omega_using [hx])]
    rw [Int.emod_eq_of_lt (by omega_using []) (by omega_using [h0]), this] at h1
    constructor <;> intro _ <;> omega_arith
  · have : x % (2 * M) = x := Int.emod_eq_of_lt hx (by omega_using [h3])
    rw [Int.emod_eq_of_lt (by omega_using []) (by omega_using [h0]), this] at h1
    constructor <;> intro _ <;> omega_arith

theorem Rep.nonneg {M w : Nat} {x : Int} (h : Rep M w x) (hx : 0 ≤ x) : (w : Int) = x := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [Int.emod_eq_of_lt (by omega_using []) (by omega_using [h0]), Int.emod_eq_of_lt hx (by omega_using [h3])] at h1; exact h1

theorem Rep.of_cong {M w : Nat} {x : Int} (hw : w < 2 * M) (hc : (w : Int) ≡ x [ZMOD (2 * M : Nat)])
    (h2 : -(M : Int) ≤ x) (h3 : x < M) : Rep M w x := ⟨hw, by exact_mod_cast hc, h2, h3⟩

/-- The top word's sign is the number's. -/
theorem top_sign {m : Mem} {W : Addr} {b n : Nat} {x : Int}
    (h : Rep (2 ^ (32 * n) * 2 ^ 31) (val32 m W b (n + 1)) x) :
    2 ^ 31 ≤ VG.Proof.Mont.w32 m W (b + 4 * n) ↔ x < 0 := by
  rw [top_iff m W b 4 n, ← val32_sv]; exact h.sign

theorem two_M (n : Nat) : 2 * (2 ^ (32 * n) * 2 ^ 31) = 2 ^ (32 * (n + 1)) := by
  rw [show 32 * (n + 1) = 32 * n + 32 by omega_using [], Nat.pow_add]; omega_using []

/-! ## `+ p` where negative -/

theorem addIfNegF_ok {s : State} (h : Bx L s B Z len N) (hn2 : 2 ≤ nw len) {p : Nat} {X : Int}
    (hp : val32 s.mem B (rv (kw len) mo) (nw len + 1) = p) (pv : p < 2 ^ (32 * nw len))
    (hX : Rep (2 ^ (32 * nw len) * 2 ^ 31) (val32 s.mem B (rv (kw len) (a 7)) (nw len + 1)) X)
    (hXr : -2 * (p : Int) ≤ X) :
    WP isa (addIfNegF L (a 7)) s fun t =>
      Bx L t B Z len N ∧
      Rep (2 ^ (32 * nw len) * 2 ^ 31) (val32 t.mem B (rv (kw len) (a 7)) (nw len + 1)) (if X < 0 then X + p else X) ∧
      Unch B [(rv (kw len) tmp, 4 * (nw len + 1)), (rv (kw len) (a 7), 4 * (nw len + 1))] s.mem t.mem ∧
      Keeps wordClob s t := by
  have hn := h.nowrap
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have r2 := rv_a len 2; have r7 := rv_a len 7; have r12 := rv_a len 12
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have rtmp : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  have h71 : rv (kw len) { (a 7) with half := 1 } = rv (kw len) (a 7) + 4 * nw len := rv_half1' len 7
  have M2 := two_M (nw len)
  have pM : (p : Int) < ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) := by
    have : 2 ^ (32 * nw len) ≤ 2 ^ (32 * nw len) * 2 ^ 31 := Nat.le_mul_of_pos_right _ (by decide)
    exact_mod_cast (show p < 2 ^ (32 * nw len) * 2 ^ 31 by omega)
  unfold addIfNegF
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine WP.seq (WP.mono (chainAdd_ok h (o := tmp) (a := a 7) (b := mo) (e := 1) (by decide) rfl
    (by omega) (by omega) (by omega) (.inr (by omega)) (.inr (by omega))) fun s₁ ⟨H₁, O₁, ⟨c, _, V₁⟩, K₁⟩ => ?_)
  refine WP.seq (maskAt_ok H₁ (x := { (a 7) with half := 1 }) (by omega)
    fun s₂ K₂ m₂ c₂ => WP.block_nil ?_)
  have top : VG.Proof.Mont.w32 s₁.mem B (rv (kw len) { (a 7) with half := 1 }) =
      VG.Proof.Mont.w32 s.mem B (rv (kw len) (a 7) + 4 * nw len) := by
    rw [h71, O₁.w32 (.inl (by omega)) (by omega)]
  rw [top] at c₂
  have H₂ : Bx L s₂ B Z len N := H₁.keep K₂ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₂]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  have mask : s₂.gpr .ecx = cmask (decide (X < 0)) := by
    rw [c₂]; simp only [cmask]
    by_cases hx : X < 0
    · simp only [(top_sign hX).mpr hx, ↓reduceIte, hx, decide_true]
    · simp only [show ¬ 2 ^ 31 ≤ VG.Proof.Mont.w32 s.mem B (rv (kw len) (a 7) + 4 * nw len) from
        fun e => hx ((top_sign hX).mp e), ↓reduceIte, hx, decide_false, Bool.false_eq_true]
  refine WP.mono (selIn_ok H₂ (o := a 7) (a := tmp) (e := 1) mask (by decide) (by omega) (by omega) (by omega))
    fun t ⟨Ht, Ot, Vt, Kt⟩ => ⟨Ht, ?_, ?_, ?_⟩
  · have a7₁ : val32 s₁.mem B (rv (kw len) (a 7)) (nw len + 1) = val32 s.mem B (rv (kw len) (a 7)) (nw len + 1) :=
      O₁.val32 (by omega) (by omega)
    have mo₁ : val32 s₁.mem B (rv (kw len) mo) (nw len + 1) = val32 s.mem B (rv (kw len) mo) (nw len + 1) :=
      O₁.val32 (by omega) (by omega)
    rw [Vt, m₂, a7₁]
    by_cases hx : X < 0
    · simp only [hx, decide_true, ↓reduceIte]
      have lt := val32_lt s₁.mem B (rv (kw len) tmp) (nw len + 1)
      rw [← M2] at lt
      have b1 := hX.2.2.1; have b2 := hX.2.2.2
      refine Rep.of_cong lt ?_ (by omega) (by omega)
      have e : (val32 s₁.mem B (rv (kw len) tmp) (nw len + 1) : Int) =
          (val32 s.mem B (rv (kw len) (a 7)) (nw len + 1) + p) +
            ((2 * (2 ^ (32 * nw len) * 2 ^ 31) : Nat) : Int) * (-(c.toNat : Int)) := by
        have V : (val32 s₁.mem B (rv (kw len) tmp) (nw len + 1) : Int) + 2 ^ (32 * (nw len + 1)) * (c.toNat : Int) =
            val32 s.mem B (rv (kw len) (a 7)) (nw len + 1) + val32 s.mem B (rv (kw len) mo) (nw len + 1) := by
          exact_mod_cast V₁
        rw [M2, ← hp]; push_cast; linarith
      have hx : ((val32 s.mem B (rv (kw len) (a 7)) (nw len + 1) : Nat) : Int) ≡ X
          [ZMOD ((2 * (2 ^ (32 * nw len) * 2 ^ 31) : Nat) : Int)] := by
        have := hX.2.1; unfold Int.ModEq; push_cast at this ⊢; exact this
      unfold Int.ModEq
      rw [e, Int.add_mul_emod_self_left]
      exact hx.add_right _
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]; exact hX
  · exact ((O₁.unch.trans (m₂ ▸ Ot).unch).mono fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with rfl | rfl <;> simp)
  · exact ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (Kt.mono (by decide))

/-- Strided words hold their two's complement value. -/
theorem rep_sval {m : Mem} {W : Addr} {b sz n : Nat}
    (h1 : -((2 ^ (32 * n) * 2 ^ 31 : Nat) : Int) ≤ sval m W b sz n)
    (h2 : sval m W b sz n < ((2 ^ (32 * n) * 2 ^ 31 : Nat) : Int)) :
    Rep (2 ^ (32 * n) * 2 ^ 31) (sv m W b sz (n + 1)) (sval m W b sz n) := by
  refine ⟨by rw [two_M]; exact sv_lt _ _ _ _ _, ?_, h1, h2⟩
  have e : ((2 * (2 ^ (32 * n) * 2 ^ 31) : Nat) : Int) = 2 ^ (32 * (n + 1)) := by rw [two_M]; push_cast; rfl
  push_cast at e ⊢
  rw [e]
  unfold sval
  split
  · rw [show (sv m W b sz (n + 1) : Int) - 2 ^ (32 * (n + 1)) =
      sv m W b sz (n + 1) + 2 ^ (32 * (n + 1)) * (-1) by ring, Int.add_mul_emod_self_left]
  · rw [Int.sub_zero]

/-- The low `n` words of a two's complement number of `n + 1`. -/
theorem Rep.low {m : Mem} {W : Addr} {b n : Nat} {x : Int}
    (h : Rep (2 ^ (32 * n) * 2 ^ 31) (val32 m W b (n + 1)) x) :
    (val32 m W b n : Int) % 2 ^ (32 * n) = x % 2 ^ (32 * n) := by
  have hc := h.2.1
  have e : (2 : Int) * ((2 ^ (32 * n) * 2 ^ 31 : Nat) : Int) = 2 ^ (32 * n) * 2 ^ 32 := by push_cast; ring
  have d : (2 : Int) ^ (32 * n) ∣ 2 ^ (32 * n) * 2 ^ 32 := Dvd.intro _ rfl
  rw [e] at hc
  have h3 : (val32 m W b (n + 1) : Int) % 2 ^ (32 * n) = x % 2 ^ (32 * n) := by
    rw [← Int.emod_emod_of_dvd (val32 m W b (n + 1) : Int) d, hc, Int.emod_emod_of_dvd _ d]
  rw [← h3, val32_succ]; push_cast
  rw [Int.add_mul_emod_self_left]

/-- `finishF`'s tail: `[1] = |f|` from `[14]` and `[3] = [7]`, `w` words each. -/
theorem finishTail_ok {s : State} (h : Bx L s B Z len N) {a₀ : Nat} {f : Int}
    (hb : |f| < 2 ^ (32 * nw len))
    (hc : (val32 s.mem B (rv (kw len) (a 14)) (nw len) : Int) % (2 ^ (32 * nw len) : Int) =
      f % (2 ^ (32 * nw len) : Int))
    (sign : (2 ^ 31 ≤ w32 s.mem B (rv (kw len) (a 14) + 4 * nw len)) ↔ f < 0)
    (coef : val32 s.mem B (rv (kw len) (a 7)) (nw len) = a₀) :
    WP isa (VG.Impl.Rsa.X86.Keys.seqs [VG.Impl.Rsa.X86.InvBatchRt.zeros L (a 1) (wBytes .ecx),
      VG.Impl.Rsa.X86.InvBatchRt.chain L .sbb (a 1) (a 1) (a 14) (nBytes .edx 0),
      .block (maskAt L { arr := 14, half := 1 } ++ [.alu .xor .ecx (.imm (-1))]),
      selIn L (a 1) (a 14) (nBytes .edi 0),
      VG.Impl.Rsa.X86.InvBatchRt.zeros L (a 3) (wBytes .ecx), VG.Impl.Rsa.X86.InvBatchRt.copy L (a 3) (a 7) (nBytes .edi 0)]) s fun z =>
      Bx L z B Z len N ∧ val32 z.mem B (rv (kw len) (a 1)) (kw len) = f.natAbs ∧
      val32 z.mem B (rv (kw len) (a 3)) (kw len) = a₀ ∧ Keeps wordClob s z ∧
      Unch B [(rv (kw len) (a 1), 4 * kw len), (rv (kw len) (a 3), 4 * kw len)] s.mem z.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have r1 := rv_a len 1; have r3 := rv_a len 3; have r4 := rv_a len 14; have r6 := rv_a len 7
  have h41 := rv_half1' len 14
  have WS : CountSpec (wBytes .ecx) .ecx B Z (kw len) (kw len) := wBytes_spec hZ (by omega_using [hw]) (by omega_using [ke])
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- `[1] = 0`, then `-[4]`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok h (o := a 1) WS hpos (by omega_using [hf16, ke, r1]))
    fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  have split1 := val32_append s₁.mem B (rv (kw len) (a 1)) (nw len) (nw len)
  rw [show nw len + nw len = kw len by omega_using [ke], V₁] at split1
  have low0 : val32 s₁.mem B (rv (kw len) (a 1)) (nw len) = 0 := by omega_using [split1]
  have tail0 : val32 s₁.mem B (rv (kw len) (a 1) + 4 * nw len) (nw len) = 0 := by
    have pow := Nat.two_pow_pos (32 * nw len)
    rcases Nat.eq_zero_or_pos (val32 s₁.mem B (rv (kw len) (a 1) + 4 * nw len) (nw len)) with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (32 * nw len)) e; omega_using [split1, pow, this]
  refine WP.seq (WP.mono (chainSub_ok H₁ (o := a 1) (a := a 1) (b := a 14) (e := 0) (by decide) rfl
    (by omega_using [hf16, ke, r1]) (by omega_using [hf16, ke, r1]) (by omega_using [hf16, ke, r4]) (.inl (Nat.le_refl _)) (by omega_using [r1, r4])) fun s₂ ⟨H₂, O₂, ⟨c, _, V₂⟩, K₂⟩ => ?_)
  simp only [Nat.add_zero] at O₂ V₂
  rw [low0, Nat.zero_add, O₁.val32 (by omega_using [ke, r1, r4]) (by omega_using [hw, ke, r4])] at V₂
  -- The selection of `[4]` where `f` is not negative.
  refine WP.seq (maskAt_ok H₂ (x := { arr := 14, half := 1 }) (by omega_using [hf16, r4, h41]) fun s₃ K₃ m₃ c₃ => ?_)
  rw [h41, O₂.w32 (by omega_using [ke, r1, r4]) (by omega_using [hn, hf16, r4]), O₁.w32 (by omega_using [ke, r1, r4]) (by omega_using [hn, hf16, r4])] at c₃
  refine wp_logicS (.inr rfl) rfl fun s₄ U₄ => WP.block_nil ?_
  have K₄ : Keeps [.eax, .ebx, .ecx, .edx] s₂ s₄ := K₃.trans (U₄.keeps.mono (by decide))
  have m₄ : s₄.mem = s₂.mem := by rw [U₄.mem, m₃]
  have H₄ : Bx L s₄ B Z len N := H₂.keep K₄ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₄]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega_using [hf16])
  have mask : s₄.gpr .ecx = cmask (!decide (f < 0)) := by
    rw [U₄.gpr, ite_eq_right (by decide), c₃]
    simp only [cmask]
    by_cases hf : f < 0
    · rw [ite_eq_left (sign.mpr hf)]; simp only [hf, decide_true, Bool.not_true]; decide
    · rw [ite_eq_right (fun e => hf (sign.mp e))]; simp only [hf, decide_false, Bool.not_false]; decide
  refine WP.seq (WP.mono (selIn_ok H₄ (o := a 1) (a := a 14) (e := 0) mask (by decide) (by omega_using [hf16, ke, r1]) (by omega_using [hf16, ke, r4])
    (by omega_using [ke, r1, r4])) fun s₅ ⟨H₅, O₅, V₅, K₅⟩ => ?_)
  simp only [Nat.add_zero] at O₅ V₅
  rw [m₄, O₂.val32 (d := rv (kw len) (a 14)) (by omega_using [ke, r1, r4]) (by omega_using [hw, ke, r4]),
    O₁.val32 (d := rv (kw len) (a 14)) (by omega_using [ke, r1, r4]) (by omega_using [hw, ke, r4])] at V₅
  have abs1 : val32 s₅.mem B (rv (kw len) (a 1)) (nw len) = f.natAbs := by
    rw [V₅]
    have := VG.Proof.Rsa.Divstep.abs_select (Nat.two_pow_pos _) hb (val32_lt _ _ _ _) (by exact_mod_cast hc) ⟨c, V₂⟩
    rw [← this]
    by_cases hf : f < 0 <;> simp [hf]
  have full1 : val32 s₅.mem B (rv (kw len) (a 1)) (kw len) = f.natAbs := by
    have sp := val32_append s₅.mem B (rv (kw len) (a 1)) (nw len) (nw len)
    rw [show nw len + nw len = kw len by omega_using [ke], abs1, O₅.val32 (d := rv (kw len) (a 1) + 4 * nw len) (by omega_using [ke])
      (by omega_using [hn, hf16, r1]), m₄, O₂.val32 (d := rv (kw len) (a 1) + 4 * nw len) (by omega_using [ke]) (by omega_using [hn, hf16, r1]), tail0, Nat.mul_zero,
      Nat.add_zero] at sp
    exact sp
  -- `[3] = [6]`, zero-padded.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok H₅ (o := a 3) WS hpos (by omega_using [hf16, ke, r3]))
    fun s₆ ⟨H₆, O₆, V₆, K₆⟩ => ?_)
  have split6 := val32_append s₆.mem B (rv (kw len) (a 3)) (nw len) (nw len)
  rw [show nw len + nw len = kw len by omega_using [ke], V₆] at split6
  have tail6 : val32 s₆.mem B (rv (kw len) (a 3) + 4 * nw len) (nw len) = 0 := by
    have pow := Nat.two_pow_pos (32 * nw len)
    rcases Nat.eq_zero_or_pos (val32 s₆.mem B (rv (kw len) (a 3) + 4 * nw len) (nw len)) with e | e
    · exact e
    · have := Nat.mul_le_mul_left (2 ^ (32 * nw len)) e; omega_using [split6, pow, this]
  refine WP.mono (copy_ok H₆ (o := a 3) (a := a 7) (e := 0) (by decide) (by omega_using [hf16, ke, r3]) (by omega_using [hf16, ke, r6]) (by omega_using [ke, r3, r6]))
    fun z ⟨Hz, O₇, V₇, K₇⟩ => ?_
  simp only [Nat.add_zero] at O₇ V₇
  refine ⟨Hz, ?_, ?_, ?_, ?_⟩
  · rw [O₇.val32 (d := rv (kw len) (a 1)) (by omega_using [ke, r1, r3]) (by omega_using [hw, ke, r1]),
      O₆.val32 (d := rv (kw len) (a 1)) (by omega_using [ke, r1, r3]) (by omega_using [hw, ke, r1]), full1]
  · have sp := val32_append z.mem B (rv (kw len) (a 3)) (nw len) (nw len)
    rw [show nw len + nw len = kw len by omega_using [ke], V₇, O₇.val32 (d := rv (kw len) (a 3) + 4 * nw len) (by omega_using [ke])
      (by omega_using [hn, hf16, r3]), tail6, Nat.mul_zero, Nat.add_zero, O₆.val32 (d := rv (kw len) (a 7)) (by omega_using [ke, r3, r6]) (by omega_using [hw, ke, r6]),
      O₅.val32 (d := rv (kw len) (a 7)) (by omega_using [ke, r1, r6]) (by omega_using [hw, ke, r6]), m₄,
      O₂.val32 (d := rv (kw len) (a 7)) (by omega_using [ke, r1, r6]) (by omega_using [hw, ke, r6]), O₁.val32 (d := rv (kw len) (a 7)) (by omega_using [ke, r1, r6]) (by omega_using [hw, ke, r6]),
      coef] at sp
    exact sp
  · exact (((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₄.mono (by decide))).trans
      (K₅.mono (by decide))).trans (K₆.mono (by decide))).trans (K₇.mono (by decide))
  · intro x hx
    have h1 := hx (rv (kw len) (a 1), 4 * kw len) (by simp)
    have h3 := hx (rv (kw len) (a 3), 4 * kw len) (by simp)
    rw [O₇ x (by omega_using [h3]), O₆ x h3, O₅ x (by omega_using [h1]), m₄, O₂ x (by omega_using [h1]), O₁ x h1]

theorem unch_val32 {W : List (Nat × Nat)} {m m' : Mem} (h : Unch B W m m') {d k : Nat}
    (hd : ∀ r ∈ W, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 * k ≤ 2 ^ 32) :
    val32 m' B d k = val32 m B d k := by
  rw [val32_sv, val32_sv]
  exact (Same.of_unch h (fun w hw r hr => by have := hd r hr; omega_using [hw, this]) fun w hw => by omega_using [hd', hw]).sv

/-! ## The end -/

theorem finishF_ok {s : State} (h : Bx L s B Z len N) (hn2 : 2 ≤ nw len) {p : Nat} {fF D : Int}
    (Ff : sval s.mem B (rv (kw len) { arr := fgArr } + fgSz + 8) fgSz (nw len) = fF)
    (Fd : sval s.mem B (rv (kw len) { arr := deArr } + deSz + 8) deSz (nw len) = D)
    (hp : val32 s.mem B (rv (kw len) (a 2)) (nw len + 1) = p) (pv : p < 2 ^ (32 * nw len)) (p0 : 0 < p)
    (hf : |fF| < 2 ^ (32 * nw len)) (hD1 : -2 * (p : Int) < D) (hD2 : D < p) :
    WP isa (finishF L) s fun z =>
      Bx L z B Z len N ∧ val32 z.mem B (rv (kw len) (a 1)) (kw len) = fF.natAbs ∧
      val32 z.mem B (rv (kw len) (a 3)) (kw len) = ((if fF < 0 then -D else D) % (p : Int)).toNat ∧
      Keeps wordClob s z ∧ Unch B (bodyWrites len) s.mem z.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have hpos := h.ws.kw_pos
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have r1 := rv_a len 1; have r2 := rv_a len 2; have r3 := rv_a len 3; have r7 := rv_a len 7
  have r12 := rv_a len 12; have r14 := rv_a len 14; have r0 := rv_a len 0; have r11 := rv_a len 11
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have rtmp : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  have hAF : rv (kw len) { arr := fgArr } = 160 + 4 * (8 * nw len + 8) := rv_a len 4
  have hAD : rv (kw len) { arr := deArr } = 160 + 11 * (8 * nw len + 8) := rv_a len 11
  have h141 : rv (kw len) { arr := 14, half := 1 } = rv (kw len) (a 14) + 4 * nw len := rv_half1' len 14
  have efs : fgSz = 16 := rfl; have eds : deSz = 20 := rfl
  have M2 := two_M (nw len)
  have Mle : 2 ^ (32 * nw len) ≤ 2 ^ (32 * nw len) * 2 ^ 31 := Nat.le_mul_of_pos_right _ (by decide)
  have MI : ((2 ^ (32 * nw len) * 2 ^ 31 : Nat) : Int) = (2 : Int) ^ (32 * nw len) * 2 ^ 31 := by push_cast; rfl
  have pI : (p : Int) < 2 ^ (32 * nw len) := by exact_mod_cast pv
  have KI : (0 : Int) < 2 ^ (32 * nw len) := two_pow_pos' _
  have big : (2 : Int) ^ (32 * nw len) * 2 ≤ 2 ^ (32 * nw len) * 2 ^ 31 := Int.mul_le_mul_of_nonneg_left (by decide) KI.le
  have CS : CountSpec (nBytes .ecx 1) .ecx B Z (kw len) (nw len + 1) := by
    have := nBytes_spec (r := .ecx) (e := 1) (B := B) hZ (w := kw len) (by omega_using [hw]) (by decide) (by omega_using [ke])
    rwa [show kw len / 2 + 1 = nw len + 1 by omega_using [ke]] at this
  unfold finishF
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  -- `f` and `d`.
  refine WP.seq (WP.mono (gather_ok h (arr := fgArr) (sz := fgSz) (x := 8) (dst := a 14) (by decide)
    (by rw [efs]; omega_using [hf16, ke, hAF]) (by omega_using [hf16, ke, r14]) (.inr (by rw [efs]; omega_using [ke, r14, hAF]))) fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  refine WP.seq (WP.mono (gather_ok H₁ (arr := deArr) (sz := deSz) (x := 8) (dst := a 7) (by decide)
    (by rw [eds]; omega_using [hf16, hpos, ke, hAD]) (by omega_using [hf16, ke, r7]) (.inl (by omega_using [ke, r7, hAD]))) fun s₂ ⟨H₂, O₂, V₂, K₂⟩ => ?_)
  rw [(Same.of_unch O₁.unch (b := rv (kw len) { arr := deArr } + deSz + 8) (sz := deSz) (K := nw len + 1)
    (fun w hw r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := Nat.mul_le_mul_left deSz (show w ≤ nw len by omega_using [hw]); rw [eds] at this ⊢; exact .inl (by omega))
    fun w hw => by
      have := Nat.mul_le_mul_left deSz (show w ≤ nw len by omega_using [hw]); rw [eds] at this ⊢; omega_using [hn, hf16, hAD, hw]).sv] at V₂
  have RF : Rep (2 ^ (32 * nw len) * 2 ^ 31) (val32 s₁.mem B (rv (kw len) (a 14)) (nw len + 1)) fF := by
    have := abs_lt.mp hf
    rw [V₁, ← Ff]; exact rep_sval (by rw [MI, Ff]; omega_using [this]) (by rw [MI, Ff]; omega_using [this])
  have RD : Rep (2 ^ (32 * nw len) * 2 ^ 31) (val32 s₂.mem B (rv (kw len) (a 7)) (nw len + 1)) D := by
    rw [V₂, ← Fd]; exact rep_sval (by rw [MI, Fd]; omega_using [hD1, pI]) (by rw [MI, Fd]; omega_using [hD2, pI])
  -- `-d`.
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.InvBatchRt.zeros_ok H₂ (o := tmp) CS (by omega_using []) (by omega_using [hf16, r12, rtmp]))
    fun s₃ ⟨H₃, O₃, Z₃, K₃⟩ => ?_)
  refine WP.seq (WP.mono (chainSub_ok H₃ (o := tmp) (a := tmp) (b := a 7) (e := 1) (by decide) rfl
    (by omega_using [hf16, ke, r12, rtmp]) (by omega_using [hf16, ke, r12, rtmp]) (by omega_using [hf16, ke, r7]) (.inl (Nat.le_refl _)) (.inr (by omega_using [ke, r7, r12, rtmp]))) fun s₄ ⟨H₄, O₄, ⟨c₄, _, V₄⟩, K₄⟩ => ?_)
  have a7₃ : val32 s₃.mem B (rv (kw len) (a 7)) (nw len + 1) = val32 s₂.mem B (rv (kw len) (a 7)) (nw len + 1) :=
    O₃.val32 (by omega_using [r7, r12, rtmp]) (by omega_using [hn, hf16, r7])
  rw [Z₃, a7₃] at V₄
  -- The sign of `f`.
  have top₄ : VG.Proof.Mont.w32 s₄.mem B (rv (kw len) (a 14) + 4 * nw len) =
      VG.Proof.Mont.w32 s₁.mem B (rv (kw len) (a 14) + 4 * nw len) := by
    rw [O₄.w32 (.inr (by omega_using [ke, r12, r14, rtmp])) (by omega_using [hn, hf16, r14]), O₃.w32 (.inr (by omega_using [r12, r14, rtmp])) (by omega_using [hn, hf16, r14]), O₂.w32 (.inr (by omega_using [ke, r7, r14])) (by omega_using [hn, hf16, r14])]
  refine WP.seq (maskAt_ok H₄ (x := { arr := 14, half := 1 }) (by omega_using [hf16, r14, h141]) fun s₅ K₅ m₅ c₅ => WP.block_nil ?_)
  rw [h141, top₄] at c₅
  have H₅ : Bx L s₅ B Z len N := H₄.keep K₅ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₅]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega_using [hf16])
  have mask : s₅.gpr .ecx = cmask (decide (fF < 0)) := by
    rw [c₅]; simp only [cmask]
    by_cases hx : fF < 0
    · simp only [(top_sign RF).mpr hx, ↓reduceIte, hx, decide_true]
    · simp only [show ¬ 2 ^ 31 ≤ VG.Proof.Mont.w32 s₁.mem B (rv (kw len) (a 14) + 4 * nw len) from
        fun e => hx ((top_sign RF).mp e), ↓reduceIte, hx, decide_false, Bool.false_eq_true]
  refine WP.seq (WP.mono (selIn_ok H₅ (o := a 7) (a := tmp) (e := 1) mask (by decide) (by omega_using [hf16, ke, r7]) (by omega_using [hf16, ke, r12, rtmp])
    (by omega_using [ke, r7, r12, rtmp])) fun s₆ ⟨H₆, O₆, V₆, K₆⟩ => ?_)
  rw [m₅, O₄.val32 (d := rv (kw len) (a 7)) (by omega_using [ke, r7, r12, rtmp]) (by omega_using [hw, ke, r7]), a7₃] at V₆
  have R₆ : Rep (2 ^ (32 * nw len) * 2 ^ 31) (val32 s₆.mem B (rv (kw len) (a 7)) (nw len + 1))
      (if fF < 0 then -D else D) := by
    rw [V₆]
    by_cases hx : fF < 0
    · simp only [hx, decide_true, ↓reduceIte]
      have lt := val32_lt s₄.mem B (rv (kw len) tmp) (nw len + 1)
      rw [← M2] at lt
      refine Rep.of_cong lt ?_ (by rw [MI]; omega_using [hD2, pI]) (by rw [MI]; omega_using [hD1, pI])
      have V : (val32 s₄.mem B (rv (kw len) tmp) (nw len + 1) : Int) =
          -(val32 s₂.mem B (rv (kw len) (a 7)) (nw len + 1) : Int) +
            ((2 * (2 ^ (32 * nw len) * 2 ^ 31) : Nat) : Int) * (c₄.toNat : Int) := by
        have V' : (val32 s₄.mem B (rv (kw len) tmp) (nw len + 1) : Int) +
            val32 s₂.mem B (rv (kw len) (a 7)) (nw len + 1) = 0 + 2 ^ (32 * (nw len + 1)) * (c₄.toNat : Int) := by
          exact_mod_cast V₄
        rw [M2]; push_cast; linarith
      have hx' : ((val32 s₂.mem B (rv (kw len) (a 7)) (nw len + 1) : Nat) : Int) ≡ D
          [ZMOD ((2 * (2 ^ (32 * nw len) * 2 ^ 31) : Nat) : Int)] := by
        have := RD.2.1; unfold Int.ModEq; push_cast at this ⊢; exact this
      unfold Int.ModEq
      rw [V, Int.add_mul_emod_self_left]
      exact hx'.neg
    · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]; exact RD
  -- `[2]` so far.
  have P₆ : val32 s₆.mem B (rv (kw len) mo) (nw len + 1) = p := by
    rw [rmo, O₆.val32 (by omega_using [r2, r7]) (by omega_using [hn, hf16, r2]), m₅, O₄.val32 (by omega_using [r2, r12, rtmp]) (by omega_using [hn, hf16, r2]), O₃.val32 (by omega_using [r2, r12, rtmp]) (by omega_using [hn, hf16, r2]),
      O₂.val32 (by omega_using [r2, r7]) (by omega_using [hn, hf16, r2]), O₁.val32 (by omega_using [r2, r14]) (by omega_using [hn, hf16, r2]), hp]
  have apA : ∀ {d k : Nat}, (d + 4 * k ≤ rv (kw len) (a 7) ∨ rv (kw len) (a 12) + 4 * (nw len + 1) ≤ d) →
      ∀ r ∈ [(rv (kw len) tmp, 4 * (nw len + 1)), (rv (kw len) (a 7), 4 * (nw len + 1))], d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith
  have apB : ∀ {d k : Nat}, (d + 4 * k ≤ rv (kw len) (a 7) ∨ rv (kw len) (a 12) + 4 * (nw len + 1) ≤ d) →
      ∀ r ∈ [(rv (kw len) tmp, 4 * nw len), (rv (kw len) (a 7), 4 * nw len)], d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d :=
    fun hd r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega_arith
  -- Into `[0, 2p)`.
  set X1 : Int := if fF < 0 then -D else D with hX1
  have x1 : -2 * (p : Int) < X1 ∧ X1 < 2 * p := by rw [hX1]; split <;> omega_using [hD1, hD2]
  refine WP.seq (WP.mono (addIfNegF_ok H₆ hn2 P₆ pv R₆ (by omega_using [hD1, hD2])) fun s₇ ⟨H₇, R₇, U₇, K₇⟩ => ?_)
  have P₇ : val32 s₇.mem B (rv (kw len) mo) (nw len + 1) = p := by
    rw [← P₆]; exact unch_val32 U₇ (apA (.inl (by omega_using [r2, r7, rmo]))) (by omega_using [hn, hf16, r2, rmo])
  set X2 : Int := if X1 < 0 then X1 + p else X1 with hX2
  have x2 : -(p : Int) ≤ X2 ∧ X2 < 2 * p := by rw [hX2]; split <;> omega_arith
  refine WP.seq (WP.mono (addIfNegF_ok H₇ hn2 P₇ pv R₇ (by omega_using [hD1, hD2])) fun s₈ ⟨H₈, R₈, U₈, K₈⟩ => ?_)
  have P₈ : val32 s₈.mem B (rv (kw len) mo) (nw len + 1) = p := by
    rw [← P₇]; exact unch_val32 U₈ (apA (.inl (by omega_using [r2, r7, rmo]))) (by omega_using [hn, hf16, r2, rmo])
  set X3 : Int := if X2 < 0 then X2 + p else X2 with hX3
  have x3 : 0 ≤ X3 ∧ X3 < 2 * p := by rw [hX3]; split <;> omega_arith
  have e₈ : (val32 s₈.mem B (rv (kw len) (a 7)) (nw len + 1) : Int) = X3 := R₈.nonneg x3.1
  have Pn : val32 s₈.mem B (rv (kw len) mo) (nw len) = p := by
    have hs := val32_succ s₈.mem B (rv (kw len) mo) (nw len)
    have hl := val32_lt s₈.mem B (rv (kw len) mo) (nw len)
    rw [P₈] at hs
    rcases Nat.eq_zero_or_pos (VG.Proof.Mont.w32 s₈.mem B (rv (kw len) mo + 4 * nw len)) with e | e
    · rw [e, Nat.mul_zero, Nat.add_zero] at hs; exact hs.symm
    · have := Nat.mul_le_mul_left (2 ^ (32 * nw len)) e; omega_using [pv, p0, hf, hD1, hD2, M2, Mle, MI, pI, KI, big, hX1, x1, hX2, x2, hX3, x3, e₈, hs, hl, e, this]
  refine WP.seq (WP.mono (csub_ok H₈ (src := a 7) (o := a 7) rfl rfl (by omega_using [hf16, r7]) (by omega_using [hf16, r7]) (by omega_using [hf16, r12, rtmp]) (by omega_using [hf16, r2, rmo])
    (.inr (by omega_using [r7, r12, rtmp])) (.inr (by omega_using [r2, r12, rmo, rtmp])) (fun h => absurd rfl h) (.inl (by omega_using [r7, r12, rtmp])) Pn (by omega_using [hD1, hD2, e₈]))
    fun s₉ ⟨H₉, U₉, V₉, K₉⟩ => ?_)
  -- `f`'s words, still.
  have F₉ : Rep (2 ^ (32 * nw len) * 2 ^ 31) (val32 s₉.mem B (rv (kw len) (a 14)) (nw len + 1)) fF := by
    rw [unch_val32 U₉ (apB (.inr (by omega_using [r12, r14]))) (by omega_using [hn, hf16, r14]), unch_val32 U₈ (apA (.inr (by omega_using [r12, r14]))) (by omega_using [hn, hf16, r14]),
      unch_val32 U₇ (apA (.inr (by omega_using [r12, r14]))) (by omega_using [hn, hf16, r14]),
      O₆.val32 (by omega_using [ke, r7, r14]) (by omega_using [hn, hf16, r14]), m₅, O₄.val32 (by omega_using [ke, r12, r14, rtmp]) (by omega_using [hn, hf16, r14]), O₃.val32 (by omega_using [r12, r14, rtmp]) (by omega_using [hn, hf16, r14]),
      O₂.val32 (by omega_using [ke, r7, r14]) (by omega_using [hn, hf16, r14])]
    exact RF
  have hc : (val32 s₉.mem B (rv (kw len) (a 14)) (nw len) : Int) % 2 ^ (32 * nw len) = fF % 2 ^ (32 * nw len) :=
    F₉.low
  refine WP.mono (finishTail_ok H₉ (a₀ := val32 s₈.mem B (rv (kw len) (a 7)) (nw len + 1) % p) hf hc
    (top_sign F₉) V₉) fun z ⟨Hz, A₁, A₃, Kz, Uz⟩ => ⟨Hz, A₁, ?_, ?_, ?_⟩
  · rw [A₃]
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega_using [p0])), Int.natCast_emod, e₈]
    -- `X3 ≡ X1 (mod p)`.
    have : X3 % p = X1 % p := by
      have e2 : X2 % p = X1 % p := by rw [hX2]; split <;> simp [Int.add_emod_right]
      have e3 : X3 % p = X2 % p := by rw [hX3]; split <;> simp [Int.add_emod_right]
      rw [e3, e2]
    rw [this]
  · exact ((((((((((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
      (K₄.mono (by decide))).trans (K₅.mono (by decide))).trans (K₆.mono (by decide))).trans K₇).trans K₈).trans
      (K₉.mono (by decide))).trans Kz)
  · have hb0 : rv (kw len) (a 0) = 160 := by rw [r0]; omega_using []
    refine (((((((((O₁.unch.trans O₂.unch).trans O₃.unch).trans O₄.unch).trans (m₅ ▸ O₆).unch).trans U₇).trans
      U₈).trans U₉).trans Uz).cover ?_)
    intro w hw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hw
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    rw [hb0, r11, rtmp] at *
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega_arith

end VG.Proof.Rsa.X86.InvBatchRt.F
