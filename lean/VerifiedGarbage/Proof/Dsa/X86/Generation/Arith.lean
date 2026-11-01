module

import VerifiedGarbage.Proof.Dsa.X86.Generation.LoadStore
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
import VerifiedGarbage.Proof.Rsa.X86.DivLoop
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.WordConst
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # p from `X` and q (A.1.1.2 steps 11.4–11.5)

`c = X mod 2 q` and `p = X − c + 1`, with `p − 1` and `(p − 1) / q` for the
generator, by RSA's fixed-count division. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- The bytes of a range apart from a change. -/
theorem outside_bytesAt {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d len : Nat}
    (hd : d + len ≤ o ∨ o + n ≤ d) (hd' : d + len < 2 ^ 64) :
    Spec.Rsa.bytesAt m' (off base d) len = Spec.Rsa.bytesAt m (off base d) len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact h _ (by rw [ofs_off base (by omega)]; omega)

/-- A frame of one range of `scratch` changes nothing outside it. -/
theorem outside_of_frame {base : Addr} {d len : Nat} {m m' : Mem} (F : Frame [⟨off base d, len⟩] m m')
    (fit : d + len ≤ 2 ^ 64) : Outside base d len m m' := by
  intro x hx
  refine F x fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  have I := Offset.lt_iff x base fit
  change ¬ ((x - off base d).toNat + 1 ≤ len)
  change (x - off base d).toNat < len ↔ d ≤ ofs base x ∧ ofs base x < d + len at I
  omega

theorem add_no_carry {a b k : Nat} {c : Bool} (h : a + 2 ^ k * c.toNat = b) (hb : b < 2 ^ k) : a = b := by
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h <;> omega

theorem sub_no_borrow {a r x k : Nat} {c : Bool} (h : a + r = x + 2 ^ k * c.toNat) (ha : a < 2 ^ k)
    (hr : r ≤ x) : a = x - r := by
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h <;> omega

/-- `k + 1` words whose value fits in `k` are that value in `k`. -/
theorem val32_low {m : Mem} {base : Addr} {d k v : Nat} (h : val32 m base d (k + 1) = v) (hv : v < 2 ^ (32 * k)) :
    val32 m base d k = v := by
  rw [val32_append] at h
  have := val32_lt m base d k
  have hm : 2 ^ (32 * k) * val32 m base (d + 4 * k) 1 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m base (d + 4 * k) 1) with h0 | h0
    · rw [h0, Nat.mul_zero]
    · have := Nat.mul_le_mul_left (2 ^ (32 * k)) h0; omega
  omega

/-- The division's arrays. -/
def divGeo (base : Addr) (size n : Nat) : VG.Proof.Rsa.X86.Div.Geometry :=
  { base := base, size := size, n := n, offsets := fun i => arr i.val }

/-- The arrays the arithmetic writes, and p in p||q||g. -/
def aRanges (pLen : Nat) : List (Nat × Nat) := [(arr 0, 4400), (sPk, pLen)]

/-- p's arithmetic: `p − 1 = X − X mod 2 q`, `(p − 1) / q` and `p`, in their
arrays and p in p||q||g. -/
theorem pArith_ok {pLen qLen : Nat} (hl : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) (hq : 20 ≤ qLen ∧ qLen ≤ 32)
    {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hsz : 73728 ≤ size) {X Q : Nat}
    (hX : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base sX) pLen) = X)
    (hQ : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base (sPk + pLen)) qLen) = Q) (hQ0 : 0 < Q) :
    WP isa (pArith pLen qLen) s fun t =>
      val32 t.mem base aPm1 (pLen / 4) = X - X % (2 * Q) ∧
      val32 t.mem base aE (pLen / 4) = (X - X % (2 * Q)) / Q ∧
      val32 t.mem base aP (pLen / 4) = X - X % (2 * Q) + 1 ∧
      Spec.Rsa.bytesAt t.mem (off base sPk) pLen = Spec.Dsa.encodeBE pLen (X - X % (2 * Q) + 1) ∧
      Outs base (aRanges pLen) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      val32 t.mem base aOne (pLen / 4) = 1 := by
  have nw := hs.nowrap
  have sl := hs.size_lt
  -- The sizes.
  obtain ⟨n, hn⟩ : ∃ n, n = pLen / 4 := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h, h = pLen / 8 := ⟨_, rfl⟩
  have h2 : 2 * h = n := by rcases hl with rfl | rfl | rfl <;> subst hn hh <;> rfl
  have h8 : 8 * h = pLen := by rcases hl with rfl | rfl | rfl <;> subst hh <;> rfl
  have n4 : 4 * n = pLen := by omega_arith
  have nle : n ≤ 96 := by omega_arith
  have npos : 0 < n := by omega_arith
  have Xlt : X < 2 ^ (32 * n) := by
    have := decodeBE_lt (Spec.Rsa.bytesAt s.mem (off base sX) pLen)
    rw [VG.Proof.Bignum.bytesAt_length, hX, show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] at this
    rwa [show 8 * pLen = 32 * n by omega_arith] at this
  have Qlt : Q < 2 ^ (32 * n) := by
    have := decodeBE_lt (Spec.Rsa.bytesAt s.mem (off base (sPk + pLen)) qLen)
    rw [VG.Proof.Bignum.bytesAt_length, hQ, show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have Q2lt : 2 * Q < 2 ^ (32 * n) := by
    have := decodeBE_lt (Spec.Rsa.bytesAt s.mem (off base (sPk + pLen)) qLen)
    rw [VG.Proof.Bignum.bytesAt_length, hQ, show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] at this
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 8 * qLen + 1 ≤ 32 * n by omega_arith)
    rw [Nat.pow_succ] at this
    omega_arith
  unfold pArith
  rw [← hn, ← hh]
  simp only [seqs]
  have sz : ∀ k, k ≤ 11 → arr k + 400 ≤ size := fun k hk => by simp only [arr]; omega_arith
  have R0 : ∀ {m m' : Mem} {o len : Nat}, Outside base o len m m' → arr 0 ≤ o → o + len ≤ arr 0 + 4400 →
      Outs base (aRanges pLen) m m' := fun O h₁ h₂ =>
    Outs.of_outside (O.mono h₁ h₂) (by simp [aRanges])
  -- X into the dividend and into its own array.
  refine WP.seq (WP.mono (loadS_ok hs (k := h) (o := aQt) (src := sX) (len := pLen) (by omega_arith)
    (by simp only [aQt, arr]; omega_arith) (by omega_arith) (by omega_arith) (by simp only [sX]; omega_arith)
    (by simp only [aQt, arr, sX]; omega_arith)) fun t₁ ⟨V₁, O₁, K₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.seq (WP.mono (loadS_ok hs₁ (k := h) (o := aX) (src := sX) (len := pLen) (by omega_arith)
    (by simp only [aX, arr]; omega_arith) (by omega_arith) (by omega_arith) (by simp only [sX]; omega_arith)
    (by simp only [aX, arr, sX]; omega_arith)) fun t₂ ⟨V₂, O₂, K₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps K₂ (by decide)
  rw [outside_bytesAt O₁ (by simp only [aQt, arr, sX]; omega_arith) (by simp only [sX]; omega_arith), hX] at V₂
  rw [hX] at V₁
  -- q, with a zero word above it.
  refine WP.seq (WP.mono (loadS_ok hs₂ (k := h) (o := aTmp) (src := sPk + pLen) (len := qLen) (by omega_arith)
    (by simp only [aTmp, arr]; omega_arith) (by omega_arith) (by omega_arith) (by simp only [sPk]; omega_arith)
    (by simp only [aTmp, arr, sPk]; omega_arith)) fun t₃ ⟨V₃, O₃, K₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  rw [outside_bytesAt O₂ (by simp only [aX, arr, sPk]; omega_arith) (by simp only [sPk]; omega_arith),
    outside_bytesAt O₁ (by simp only [aQt, arr, sPk]; omega_arith) (by simp only [sPk]; omega_arith), hQ] at V₃
  refine WP.seq (wp_movi fun t₃' u₃ => st_ok (Scr.of_eq hs₃ (u₃.other _ (by decide)) (u₃.other _ (by decide))
    u₃.wr) (d := aTmp + 4 * n) (by simp only [aTmp, arr]; omega_arith) fun t₄ M₄ => WP.block_nil ?_)
  have m₄ : t₄.mem = t₃.mem.writeW (off base (aTmp + 4 * n)) (0 : BitVec 32) := by rw [M₄.mem, u₃.mem, u₃.gpr]
  have O₄ : Outside base (aTmp + 4 * n) 4 t₃.mem t₄.mem := m₄ ▸ writeW32_outside _ _ _ (by simp only [aTmp, arr]; omega_arith)
  have K₄ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t₃ t₄ :=
    ⟨fun r hr => by rw [M₄.gpr, u₃.other r (fun e => hr (e ▸ List.mem_cons_self ..))], by rw [M₄.rd, u₃.rd],
      by rw [M₄.wr, u₃.wr]⟩
  have hs₄ := hs₃.of_keeps K₄ (by decide)
  have V₄ : val32 t₄.mem base aTmp (n + 1) = Q := by
    have V₃' : val32 t₃.mem base aTmp n = Q := by rw [← h2]; exact V₃
    rw [val32_append, O₄.val32 (by omega_arith) (by simp only [aTmp, arr]; omega_arith), V₃']
    simp only [val32, m₄, w32_write_self]
    show Q + 2 ^ (32 * n) * (0 + 2 ^ 32 * 0) = Q
    simp only [Nat.mul_zero, Nat.add_zero]
  -- The divisor `2 q`.
  refine WP.seq (WP.mono (chainAddW_ok hs₄ (k := n + 1) (o := aDv) (a := aTmp) (b := aTmp) (by omega_arith)
    (by simp only [aDv, arr]; omega_arith) (by simp only [aTmp, arr]; omega_arith) (by simp only [aTmp, arr]; omega_arith)
    (by simp only [aDv, aTmp, arr]; omega_arith) (by simp only [aDv, aTmp, arr]; omega_arith))
    fun t₅ ⟨O₅, ⟨c₅, _, E₅⟩, K₅⟩ => ?_)
  have hs₅ := hs₄.of_keeps K₅ (by decide)
  rw [V₄] at E₅
  have V₅ : val32 t₅.mem base aDv (n + 1) = 2 * Q :=
    add_no_carry (E₅.trans (by omega_arith)) (by rw [pow32_succ]; have := Nat.two_pow_pos (32 * n); omega_arith)
  -- The quotient and remainder.
  have X₅ : val32 t₅.mem base aQt n = X := by
    rw [O₅.val32 (by simp only [aDv, aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith),
      O₄.val32 (by simp only [aTmp, aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith),
      O₃.val32 (by simp only [aTmp, aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith),
      O₂.val32 (by simp only [aX, aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith), ← h2, V₁]
  have ctx : VG.Proof.Rsa.X86.Div.Context (divGeo base size n) t₅ := by
    refine ⟨hs₅, npos, by show n < 2 ^ 24; omega_arith, fun i => ?_, fun i j ne => ?_⟩
    · have := i.isLt
      show arr i.val + 4 * (if i = 0 then n else n + 1) ≤ size
      have := sz i.val (by omega_arith)
      split <;> omega_arith
    · have hij : i.val ≠ j.val := fun e => ne (Fin.ext e)
      have := i.isLt; have := j.isLt
      show arr i.val + 4 * (if i = 0 then n else n + 1) ≤ arr j.val ∨
        arr j.val + 4 * (if j = 0 then n else n + 1) ≤ arr i.val
      simp only [arr]
      split <;> split <;> omega_arith
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.Div.code_ok ctx) fun t₆ ⟨_, Os₆, K₆, R₆⟩ => ?_)
  have v0 : ∀ m, (divGeo base size n).value m 0 = val32 m base aQt n := fun _ => rfl
  have v1 : ∀ m, (divGeo base size n).value m 1 = val32 m base aRm (n + 1) := fun _ => rfl
  have v2 : ∀ m, (divGeo base size n).value m 2 = val32 m base aDv (n + 1) := fun _ => rfl
  rw [v2, V₅] at R₆
  obtain ⟨R₆, Q₆⟩ := R₆ (by omega_arith) Q2lt
  rw [v1, v0, X₅] at R₆
  rw [v0, v0, X₅] at Q₆
  have hs₆ := hs₅.of_keeps K₆ (by decide)
  have Ofar : ∀ {d k : Nat}, 4 ≤ d → d ≤ 10 → k ≤ n →
      val32 t₆.mem base (arr d) k = val32 t₅.mem base (arr d) k := fun h₁ h₂ hk =>
    Os₆.val32 (fun r hr => by
      simp only [VG.Proof.Rsa.X86.Div.Geometry.ranges, divGeo, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [arr] <;> omega_arith) (by simp only [arr]; omega_arith)
  -- `p − 1 = X − X mod 2 q`.
  have M₆ : X % (2 * Q) < 2 ^ (32 * n) := Nat.lt_of_le_of_lt (Nat.mod_le _ _) Xlt
  have Rm₆ : val32 t₆.mem base aRm n = X % (2 * Q) := val32_low R₆ M₆
  have X₆ : val32 t₆.mem base aX n = X := by
    rw [show aX = arr 4 from rfl, Ofar (by decide) (by decide) (Nat.le_refl _),
      O₅.val32 (by simp only [aDv, arr]; omega_arith) (by simp only [arr]; omega_arith),
      O₄.val32 (by simp only [aTmp, arr]; omega_arith) (by simp only [arr]; omega_arith),
      O₃.val32 (by simp only [aTmp, arr]; omega_arith) (by simp only [arr]; omega_arith), ← h2]
    exact V₂
  refine WP.seq (WP.mono (chainSubW_ok hs₆ (k := n) (o := aPm1) (a := aX) (b := aRm) npos
    (by simp only [aPm1, arr]; omega_arith) (by simp only [aX, arr]; omega_arith) (by simp only [aRm, arr]; omega_arith)
    (by simp only [aPm1, aX, arr]; omega_arith) (by simp only [aPm1, aRm, arr]; omega_arith))
    fun t₇ ⟨O₇, ⟨c₇, _, E₇⟩, K₇⟩ => ?_)
  have hs₇ := hs₆.of_keeps K₇ (by decide)
  rw [Rm₆, X₆] at E₇
  have P₇ : val32 t₇.mem base aPm1 n = X - X % (2 * Q) :=
    sub_no_borrow E₇ (val32_lt _ _ _ _) (Nat.mod_le _ _)
  -- `(p − 1) / q = 2 ⌊X / 2 q⌋`.
  have Qt₇ : val32 t₇.mem base aQt n = X / (2 * Q) := by
    rw [O₇.val32 (by simp only [aPm1, aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith), Q₆]
  have dm := Nat.div_add_mod X (2 * Q)
  have dle : X / (2 * Q) ≤ Q * (X / (2 * Q)) := Nat.le_mul_of_pos_left _ hQ0
  have dQ : 2 * Q * (X / (2 * Q)) = 2 * (Q * (X / (2 * Q))) := Nat.mul_assoc _ _ _
  refine WP.seq (WP.mono (chainAddW_ok hs₇ (k := n) (o := aE) (a := aQt) (b := aQt) npos
    (by simp only [aE, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith) (by simp only [aQt, arr]; omega_arith)
    (by simp only [aE, aQt, arr]; omega_arith) (by simp only [aE, aQt, arr]; omega_arith))
    fun t₈ ⟨O₈, ⟨c₈, _, E₈⟩, K₈⟩ => ?_)
  have hs₈ := hs₇.of_keeps K₈ (by decide)
  rw [Qt₇] at E₈
  have E₈' : val32 t₈.mem base aE n = (X - X % (2 * Q)) / Q := by
    rw [add_no_carry E₈ (by omega_arith)]
    rw [show X - X % (2 * Q) = Q * (2 * (X / (2 * Q))) by
      rw [Nat.mul_left_comm, ← Nat.mul_assoc]; omega_arith, Nat.mul_div_cancel_left _ hQ0]
    omega_arith
  have P₈ : val32 t₈.mem base aPm1 n = X - X % (2 * Q) := by
    rw [O₈.val32 (by simp only [aE, aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), P₇]
  -- 1, and `p`.
  refine WP.seq (WP.mono (setConstW_ok hs₈ (k := n) (o := aOne) (x := 1) npos
    (by simp only [aOne, arr]; omega_arith) (Nat.one_lt_two_pow (by omega_arith)))
    fun t₉ ⟨V₉, K₉, O₉⟩ => ?_)
  have hs₉ := hs₈.of_keeps K₉ (by decide)
  have P₉ : val32 t₉.mem base aPm1 n = X - X % (2 * Q) := by
    rw [O₉.val32 (by simp only [aOne, aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), P₈]
  have E₉ : val32 t₉.mem base aE n = (X - X % (2 * Q)) / Q := by
    rw [O₉.val32 (by simp only [aOne, aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith), E₈']
  refine WP.seq (WP.mono (chainAddW_ok hs₉ (k := n) (o := aP) (a := aPm1) (b := aOne) npos
    (by simp only [aP, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith)
    (by simp only [aP, aPm1, arr]; omega_arith) (by simp only [aP, aOne, arr]; omega_arith))
    fun t₁₀ ⟨O₁₀, ⟨c₁₀, _, E₁₀⟩, K₁₀⟩ => ?_)
  have hs₁₀ := hs₉.of_keeps K₁₀ (by decide)
  rw [P₉, V₉] at E₁₀
  have half : 2 ^ (32 * n) = 2 * 2 ^ (32 * n - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, 32 * n = k + 1 := ⟨32 * n - 1, by omega_arith⟩
    rw [hk, Nat.pow_succ, Nat.mul_comm, Nat.add_sub_cancel]
  have P₁₀ : val32 t₁₀.mem base aP n = X - X % (2 * Q) + 1 := add_no_carry E₁₀ (by omega_arith)
  have Pm₁₀ : val32 t₁₀.mem base aPm1 n = X - X % (2 * Q) := by
    rw [O₁₀.val32 (by simp only [aP, aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), P₉]
  have E₁₀' : val32 t₁₀.mem base aE n = (X - X % (2 * Q)) / Q := by
    rw [O₁₀.val32 (by simp only [aP, aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith), E₉]
  -- p into p||q||g.
  refine WP.mono (storeS_ok hs₁₀ (o := aP) (dst := sPk) (len := pLen) (n := h) (by omega_arith) (by omega_arith)
    (by simp only [aP, arr]; omega_arith) (by simp only [sPk]; omega_arith) (by simp only [aP, sPk, arr]; omega_arith)
    (by rw [h2, P₁₀, show 8 * pLen = 32 * n by omega_arith]; omega_arith)) fun t ⟨B₁₁, F₁₁, K₁₁⟩ => ?_
  have O₁₁ := outside_of_frame F₁₁ (by simp only [sPk]; omega_arith)
  rw [h2, P₁₀] at B₁₁
  refine ⟨?_, ?_, ?_, B₁₁, ?_, ?_, ?_⟩
  · rw [O₁₁.val32 (by simp only [aPm1, sPk, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), Pm₁₀]
  · rw [O₁₁.val32 (by simp only [aE, sPk, arr]; omega_arith) (by simp only [aE, arr]; omega_arith), E₁₀']
  · rw [O₁₁.val32 (by simp only [aP, sPk, arr]; omega_arith) (by simp only [aP, arr]; omega_arith), P₁₀]
  · have Os₆' : Outs base (aRanges pLen) t₅.mem t₆.mem := fun x hx => Os₆ x fun r hr => by
      have := hx (arr 0, 4400) (by simp [aRanges])
      simp only [VG.Proof.Rsa.X86.Div.Geometry.ranges, divGeo, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      simp only [arr] at this
      rcases hr with rfl | rfl | rfl <;> simp only [arr, divGeo, Fin.val_zero, Fin.val_one] <;> omega_arith
    refine (R0 O₁ (by simp only [aQt]; omega_arith) (by simp only [aQt, arr]; omega_arith)).trans
      ((R0 O₂ (by simp only [aX, arr]; omega_arith) (by simp only [aX, arr]; omega_arith)).trans
      ((R0 O₃ (by simp only [aTmp, arr]; omega_arith) (by simp only [aTmp, arr]; omega_arith)).trans
      ((R0 O₄ (by simp only [aTmp, arr]; omega_arith) (by simp only [aTmp, arr]; omega_arith)).trans
      ((R0 O₅ (by simp only [aDv, arr]; omega_arith) (by simp only [aDv, arr]; omega_arith)).trans
      (Os₆'.trans
      ((R0 O₇ (by simp only [aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith)).trans
      ((R0 O₈ (by simp only [aE, arr]; omega_arith) (by simp only [aE, arr]; omega_arith)).trans
      ((R0 O₉ (by simp only [aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith)).trans
      ((R0 O₁₀ (by simp only [aP, arr]; omega_arith) (by simp only [aP, arr]; omega_arith)).trans
      (Outs.of_outside O₁₁ (by simp [aRanges])))))))))))
  · exact K₁.trans (K₂.trans (K₃.trans (K₄.trans ((K₅.mono (by decide)).trans ((K₆.mono (by decide)).trans
      ((K₇.mono (by decide)).trans ((K₈.mono (by decide)).trans ((K₉.mono (by decide)).trans
      ((K₁₀.mono (by decide)).trans (K₁₁.mono (by decide)))))))))))
  · rw [O₁₁.val32 (by simp only [aOne, sPk, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith),
      O₁₀.val32 (by simp only [aP, aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith), V₉]

end VG.Proof.Dsa.X86.Generation
