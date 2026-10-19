module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# RSA private keys on AArch64: bases and loops over the words

The bases of the arrays, computed from `x0` and the stride in `x11`
(`base_ok`), and the loops of the routines of `Impl/Rsa/AArch64/Keys.lean`
that the proofs of `vg_rsa_public` and `vg_rsa_private_crt` do not already
cover: a shift left by a bit in place (`shl_ok`), a masked subtraction in
place or not (`subM_ok`), a shift right by a bit in place or not (`shr_ok`),
a masked swap (`cswap_ok`) and the `OR` of the words of an `XOR`
(`xor_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## Bases -/

theorem slot_succ (w j : Nat) : slot w (j + 1) = slot w j + 8 * (w + 2) := by
  unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega_using []

/-- `r += x11`: the base of the next array. -/
theorem addStride_ok (s : State) (r : Reg) {B : Addr} {w j : Nat} (hr : s.gpr r = off B (slot w j))
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hc : writesOnly [r] (.block [.add .x r r .x11]) = true := by decide)
    (hv : Code.allInstrs keepsV (.block [.add .x r r .x11] : Prog isa) = true := by decide +kernel) :
    WP isa (.block [.add .x r r .x11]) s fun t =>
      (t.gpr r = off B (slot w (j + 1)) ∧ t.mem = s.mem ∧ t.c = s.c) ∧ Keep [r] s t := by
  refine WP.keep (c := .block [.add .x r r .x11]) [r] ?_ hc rfl hv
  brun [hr, h11, slot_succ]

/-- `baseRep j r`: `r := x0 + 256 + j · x11`. -/
theorem baseRep_ok {s : State} {B : Addr} {w : Nat} (j : Nat) (r : Reg)
    (h0 : s.gpr .x0 = B) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hr : r ≠ .x11 := by decide)
    (hc₀ : writesOnly [r] (.block [.addImm .x r .x0 hdrBytes]) = true := by decide)
    (hv₀ : Code.allInstrs keepsV (.block [.addImm .x r .x0 hdrBytes] : Prog isa) = true := by decide +kernel)
    (hc : writesOnly [r] (.block [.add .x r r .x11]) = true := by decide)
    (hv : Code.allInstrs keepsV (.block [.add .x r r .x11] : Prog isa) = true := by decide +kernel) :
    WP isa (.block (baseRep j r)) s fun t =>
      (t.gpr r = off B (slot w j) ∧ t.mem = s.mem ∧ t.c = s.c) ∧ Keep [r] s t := by
  unfold baseRep
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep (c := .block [.addImm .x r .x0 hdrBytes]) [r]
      (Q := fun t => t.gpr r = off B (slot w 0) ∧ t.mem = s.mem ∧ t.c = s.c) (by brun [h0]; simp [off, slot]) hc₀ rfl hv₀)
    fun t₁ ⟨h₁, k₁⟩ => ?_
  have h11₁ : t₁.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr .x11 (by simp [hr.symm])).trans h11
  suffices ∀ n, ∀ t, t.gpr r = off B (slot w (j - n)) → t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) → n ≤ j →
      WP isa (.block (List.replicate n (.add .x r r .x11))) t fun t' =>
        (t'.gpr r = off B (slot w j) ∧ t'.mem = t.mem ∧ t'.c = t.c) ∧ Keep [r] t t' by
    refine WP.mono (this j t₁ (by rw [Nat.sub_self]; exact h₁.1) h11₁ (Nat.le_refl _))
      fun t ⟨⟨h, m, c⟩, k⟩ => ⟨⟨h, m.trans h₁.2.1, c.trans h₁.2.2⟩, (k₁.trans k).mono (by simp)⟩
  intro n
  induction n with
  | zero => intro t h _ _; exact WP.block_nil ⟨⟨by rwa [Nat.sub_zero] at h, rfl, rfl⟩, Keep.refl _ _⟩
  | succ n ih =>
    intro t h h11t hn
    rw [List.replicate_succ, show (Instr.add .x r r .x11 :: List.replicate n (.add .x r r .x11)) =
      [.add .x r r .x11] ++ List.replicate n (.add .x r r .x11) from rfl, WP.block_append_iff]
    refine WP.mono (addStride_ok t r h h11t hc hv) fun t₁ ⟨⟨h₁, m₁, c₁⟩, k₁⟩ => ?_
    rw [show j - (n + 1) + 1 = j - n by omega_using [hn]] at h₁
    refine WP.mono (ih t₁ h₁ ((k₁.gpr .x11 (by simp [hr.symm])).trans h11t) (by omega_using [hn]))
      fun t' ⟨⟨h', m', c'⟩, k'⟩ => ⟨⟨h', m'.trans m₁, c'.trans c₁⟩, (k₁.trans k').mono (by simp)⟩

theorem dbl_wo (r : Reg) : writesOnly [r] (.block [.add .x r r r]) = true := by cases r <;> decide
theorem dbl_kv (r : Reg) : Code.allInstrs keepsV (.block [.add .x r r r] : Prog isa) = true := by
  cases r <;> decide +kernel
theorem str_wo (r : Reg) : writesOnly [r] (.block [.add .x r r .x11]) = true := by cases r <;> decide
theorem str_kv (r : Reg) : Code.allInstrs keepsV (.block [.add .x r r .x11] : Prog isa) = true := by
  cases r <;> decide +kernel
theorem mov_wo (r : Reg) : writesOnly [r] (.block [.addImm .x r .x11 0]) = true := by cases r <;> decide
theorem mov_kv (r : Reg) : Code.allInstrs keepsV (.block [.addImm .x r .x11 0] : Prog isa) = true := by
  cases r <;> decide +kernel
theorem fin_wo (r : Reg) : writesOnly [r] (.block [.add .x r r .x0, .addImm .x r r hdrBytes]) = true := by
  cases r <;> decide
theorem fin_kv (r : Reg) :
    Code.allInstrs keepsV (.block [.add .x r r .x0, .addImm .x r r hdrBytes] : Prog isa) = true := by
  cases r <;> decide +kernel

/-- `mulBitsF r f j`: `r := j · S`, from `r = S` and `x11 = S`, for `1 ≤ j ≤ f`. -/
theorem mulBitsF_ok {r : Reg} (hr : r ≠ .x11) {S : Nat} :
    ∀ f j, 1 ≤ j → j ≤ f → ∀ t : State, t.gpr r = BitVec.ofNat 64 S → t.gpr .x11 = BitVec.ofNat 64 S →
      WP isa (.block (mulBitsF r f j)) t fun t' =>
        (t'.gpr r = BitVec.ofNat 64 (j * S) ∧ t'.mem = t.mem ∧ t'.c = t.c) ∧ Keep [r] t t'
  | 0, _, hj, hf, _, _, _ => absurd (Nat.le_trans hj hf) (by decide)
  | f + 1, j, hj, hf, t, hrv, h11 => by
    rw [mulBitsF]
    by_cases hj2 : j < 2
    · simp only [hj2, ↓reduceIte]
      exact WP.block_nil ⟨⟨by rw [hrv, show j = 1 by omega_using [hj, hj2], Nat.one_mul], rfl, rfl⟩, Keep.refl _ _⟩
    simp only [hj2, ↓reduceIte]
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (mulBitsF_ok hr f (j / 2) (by omega_using [hj2]) (by omega_using [hf]) t hrv h11) fun t₁ ⟨⟨h₁, m₁, c₁⟩, k₁⟩ => ?_
    have h11₁ : t₁.gpr .x11 = BitVec.ofNat 64 S := (k₁.gpr .x11 (by simp [hr.symm])).trans h11
    refine WP.mono (WP.keep (c := .block [.add .x r r r]) [r]
      (Q := fun t₂ => t₂.gpr r = BitVec.ofNat 64 (2 * (j / 2) * S) ∧ t₂.mem = t₁.mem ∧ t₂.c = t₁.c)
      (by
        brun [h₁]
        rw [BitVec.ofNat_add_ofNat, show j / 2 * S + j / 2 * S = 2 * (j / 2) * S by rw [Nat.mul_assoc, Nat.two_mul]])
      (dbl_wo r) rfl (dbl_kv r)) fun t₂ ⟨⟨h₂, m₂, c₂⟩, k₂⟩ => ?_
    have h11₂ : t₂.gpr .x11 = BitVec.ofNat 64 S := (k₂.gpr .x11 (by simp [hr.symm])).trans h11₁
    by_cases hb : j % 2 = 1
    · simp only [hb, ↓reduceIte]
      have hj' : 2 * (j / 2) * S + S = j * S := by
        have := Nat.div_add_mod j 2
        rw [hb] at this
        calc 2 * (j / 2) * S + S = (2 * (j / 2) + 1) * S := by rw [Nat.add_mul, Nat.one_mul]
          _ = j * S := by rw [this]
      exact WP.mono (WP.keep (c := .block [.add .x r r .x11]) [r]
        (Q := fun t₃ => t₃.gpr r = BitVec.ofNat 64 (j * S) ∧ t₃.mem = t₂.mem ∧ t₃.c = t₂.c)
        (by brun [h₂, h11₂]; rw [BitVec.ofNat_add_ofNat, hj'])
        (str_wo r) rfl (str_kv r)) fun t₃ ⟨⟨h₃, m₃, c₃⟩, k₃⟩ =>
          ⟨⟨h₃, m₃.trans (m₂.trans m₁), c₃.trans (c₂.trans c₁)⟩, ((k₁.trans k₂).trans k₃).mono (by simp)⟩
    · simp only [hb, ↓reduceIte]
      refine WP.block_nil ⟨⟨?_, m₂.trans m₁, c₂.trans c₁⟩, (k₁.trans k₂).mono (by simp)⟩
      rw [h₂]
      congr 1
      have := Nat.div_add_mod j 2
      rw [show j % 2 = 0 by omega_using [hb], Nat.add_zero] at this
      rw [this]

/-- `base j r`: `r := x0 + 256 + j · x11`, the base of array `j`. -/
theorem base_ok {s : State} {B : Addr} {w : Nat} (j : Nat) (r : Reg)
    (h0 : s.gpr .x0 = B) (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)))
    (hr : r ≠ .x11 := by decide)
    (hc₀ : writesOnly [r] (.block [.addImm .x r .x0 hdrBytes]) = true := by decide)
    (hv₀ : Code.allInstrs keepsV (.block [.addImm .x r .x0 hdrBytes] : Prog isa) = true := by decide +kernel)
    (hc : writesOnly [r] (.block [.add .x r r .x11]) = true := by decide)
    (hv : Code.allInstrs keepsV (.block [.add .x r r .x11] : Prog isa) = true := by decide +kernel) :
    WP isa (.block (base j r)) s fun t =>
      (t.gpr r = off B (slot w j) ∧ t.mem = s.mem ∧ t.c = s.c) ∧ Keep [r] s t := by
  unfold base
  by_cases hj : j = 0 ∨ r = .x0
  · simp only [hj, ↓reduceIte]
    exact baseRep_ok j r h0 h11 hr hc₀ hv₀ hc hv
  have hr0 : r ≠ .x0 := fun h => hj (.inr h)
  have hj0 : j ≠ 0 := fun h => hj (.inl h)
  simp only [hj, ↓reduceIte]
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep (c := .block [.addImm .x r .x11 0]) [r]
    (Q := fun t₁ => t₁.gpr r = BitVec.ofNat 64 (8 * (w + 2)) ∧ t₁.mem = s.mem ∧ t₁.c = s.c)
    (by brun [h11]) (mov_wo r) rfl (mov_kv r)) fun t₁ ⟨⟨h₁, m₁, c₁⟩, k₁⟩ => ?_
  have h11₁ : t₁.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr .x11 (by simp [hr.symm])).trans h11
  refine WP.mono (mulBitsF_ok hr j j (by omega_using [hj0]) (Nat.le_refl _) t₁ h₁ h11₁) fun t₂ ⟨⟨h₂, m₂, c₂⟩, k₂⟩ => ?_
  have h0₂ : t₂.gpr .x0 = B := (k₂.gpr .x0 (by simp [hr0.symm])).trans ((k₁.gpr .x0 (by simp [hr0.symm])).trans h0)
  exact WP.mono (WP.keep (c := .block [.add .x r r .x0, .addImm .x r r hdrBytes]) [r]
    (Q := fun t₃ => t₃.gpr r = off B (slot w j) ∧ t₃.mem = t₂.mem ∧ t₃.c = t₂.c)
    (by
      brun [h₂, h0₂]
      simp only [off, slot]
      rw [BitVec.add_comm (BitVec.ofNat 64 (j * (8 * (w + 2)))) B, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      congr 2
      omega_using [])
    (fin_wo r) rfl (fin_kv r)) fun t₃ ⟨⟨h₃, m₃, c₃⟩, k₃⟩ =>
      ⟨⟨h₃, m₃.trans (m₂.trans m₁), c₃.trans (c₂.trans c₁)⟩, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `ws`: `w` and the stride from the header. -/
theorem ws_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 8 * 32 ≤ Z)
    (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hS : word s.mem B (8 * sStride) = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block ws) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧
        t.c = s.c) ∧ Keep [.x11, .x12] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [hZ, hi])
  refine WP.keep [.x11, .x12] ?_ (by decide) (by decide) (by decide +kernel)
  unfold ws
  brun [h0, hl sW (by decide), hl sStride (by decide)]
  exact ⟨hW, hS⟩

/-! ## Shift left by a bit, in place -/

/-- After `j` words of `shlBody` in place at `e`: `X_j' + 2^(64 j) C = 2 X_j + c₀`
for the carry flag `C`. -/
structure ShlInv (s₀ : State) (B : Addr) (Z e : Nat) (c₀ : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x14, .x16] s₀ t
  x16 : t.gpr .x16 = off B (e + 8 * j)
  out : Outside B e (8 * j) s₀.mem t.mem
  val : wv t.mem B e j + 2 ^ (64 * j) * t.c.toNat = 2 * wv s₀.mem B e j + c₀.toNat

theorem shlStep_ok {s₀ : State} {B : Addr} {Z w e : Nat} {c₀ : Bool} (he : e + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : ShlInv s₀ B Z e c₀ j t) :
    WP isa (.block (shlBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      ShlInv s₀ B Z e c₀ (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (e + 8 * j)) (word t.mem B (e + 8 * j) + word t.mem B (e + 8 * j) +
        BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (e + 8 * j)).toNat + (word t.mem B (e + 8 * j)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x16 = off B (e + 8 * j + 8))
    (by unfold shlBody; brun [hI.x16, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega_using [he, hj]),
      hI.scr.st (show e + 8 * j + 8 ≤ Z by omega_using [he, hj])])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h16⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hy : word t.mem B (e + 8 * j) = word s₀.mem B (e + 8 * j) := hI.out.word (by omega_using []) (by omega_using [he, hj, hn])
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [he, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [he, hj, hn]), hc', hc]
    have hs := adcs_toNat (word t.mem B (e + 8 * j)) (word t.mem B (e + 8 * j)) t.c
    rw [hy] at hs
    have hval := hI.val
    simp only [wv]
    rw [pow64_succ, hy]
    grind

/-- `countLoop .x14 shlBody` over `N` words at `e`: `X' + 2^(64 N) C' = 2 X + C`
for the carry flag `C` on entry and `C'` on exit. -/
theorem shl_ok {s : State} {B : Addr} {Z N e : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B e) (h14 : s.gpr .x14 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (he : e + 8 * N ≤ Z) :
    WP isa (countLoop .x14 shlBody) s fun t =>
      wv t.mem B e N + 2 ^ (64 * N) * t.c.toNat = 2 * wv s.mem B e N + s.c.toNat ∧
      t.gpr .x16 = off B (e + 8 * N) ∧ Outside B e (8 * N) s.mem t.mem ∧ Keep [.x3, .x14, .x16] s t := by
  have h0 : ShlInv s B Z e s.c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, Outside.refl _ _ _ _, by simp [wv]⟩
  refine WP.mono (wp_countdown (N := N) (by omega_using [hN']) (by omega_using [hN]) (ShlInv s B Z e s.c)
    (fun j hj t hI _ => shlStep_ok he hj hI) h0 h14) fun t hI => ⟨hI.val, hI.x16, hI.out, hI.keep⟩

/-! ## Masked subtraction, in place or not -/

/-- After `j` words of `subMBody` from `s₀`: `O_j + (c ? Y_j : 0) = X_j + 2^(64 j) b`
for the borrow `b`, the complement of the carry flag. -/
structure SubMInv (s₀ : State) (B : Addr) (Z eo eX eY : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x8, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eY + 8 * j)
  x8 : t.gpr .x8 = off B (eo + 8 * j)
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : wv t.mem B eo j + (if c then wv s₀.mem B eY j else 0) = wv s₀.mem B eX j + 2 ^ (64 * j) * (!t.c).toNat

theorem subMStep_ok {s₀ : State} {B : Addr} {Z w eo eX eY : Nat} {c : Bool} (h15 : s₀.gpr .x15 = mask c)
    (ho : eo + 8 * w ≤ Z) (hX : eX + 8 * w ≤ Z) (hY : eY + 8 * w ≤ Z)
    (sX : eo = eX ∨ eX + 8 * w ≤ eo ∨ eo + 8 * w ≤ eX) (sY : eY + 8 * w ≤ eo ∨ eo + 8 * w ≤ eY)
    {j : Nat} (hj : j < w) {t : State} (hI : SubMInv s₀ B Z eo eX eY c j t) :
    WP isa (.block (subMBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      SubMInv s₀ B Z eo eX eY c (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x8, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eo + 8 * j)) (word t.mem B (eX + 8 * j) +
        ~~~(word t.mem B (eY + 8 * j) &&& mask c) + BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eX + 8 * j)).toNat + (~~~(word t.mem B (eY + 8 * j) &&& mask c)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eY + 8 * j + 8) ∧
      t₁.gpr .x8 = off B (eo + 8 * j + 8))
    (by unfold subMBody; brun [hI.x16, hI.x17, hI.x8, t15, hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega_using [hX, hj]),
      hI.scr.ld (show eY + 8 * j + 8 ≤ Z by omega_using [hY, hj]), hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega_using [ho, hj])])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h16, h17, h8⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eX + 8 * j) = word s₀.mem B (eX + 8 * j) := hI.out.word (by omega_using [sX, hj]) (by omega_using [hX, hj, hn])
  have hy : word t.mem B (eY + 8 * j) = word s₀.mem B (eY + 8 * j) := hI.out.word (by omega_using [sY, hj]) (by omega_using [hY, hj, hn])
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x8 (by decide), h8, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [ho, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [ho, hj, hn]), hc', hc]
    have hs := sbcs_toNat (word t.mem B (eX + 8 * j)) (word t.mem B (eY + 8 * j) &&& mask c) t.c
    rw [hx, hy, and_mask_toNat] at hs
    have hval := hI.val
    simp only [wv]
    rw [pow64_succ, hx, hy]
    cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at hs hval ⊢ <;> grind

/-- `countLoop .x14 subMBody` over `N` words: `O + (c ? Y : 0) = X + 2^(64 N) b`
for the borrow `b` out, from the carry flag set; `O` may be `X`. -/
theorem subM_ok {s : State} {B : Addr} {Z N eo eX eY : Nat} {c : Bool} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h17 : s.gpr .x17 = off B eY) (h8 : s.gpr .x8 = off B eo)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 N) (h15 : s.gpr .x15 = mask c) (hc : s.c = true)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hX : eX + 8 * N ≤ Z) (hY : eY + 8 * N ≤ Z)
    (sX : eo = eX ∨ eX + 8 * N ≤ eo ∨ eo + 8 * N ≤ eX) (sY : eY + 8 * N ≤ eo ∨ eo + 8 * N ≤ eY) :
    WP isa (countLoop .x14 subMBody) s fun t =>
      wv t.mem B eo N + (if c then wv s.mem B eY N else 0) = wv s.mem B eX N + 2 ^ (64 * N) * (!t.c).toNat ∧
      Outside B eo (8 * N) s.mem t.mem ∧ Keep [.x3, .x4, .x8, .x14, .x16, .x17] s t := by
  have h0 : SubMInv s B Z eo eX eY c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h8]; rfl, Outside.refl _ _ _ _,
      by rw [hc]; cases c <;> rfl⟩
  refine WP.mono (wp_countdown (N := N) (by omega_using [hN']) (by omega_using [hN]) (SubMInv s B Z eo eX eY c)
    (fun j hj t hI _ => subMStep_ok h15 ho hX hY sX sY hj hI) h0 h14) fun t hI => ⟨hI.val, hI.out, hI.keep⟩

/-! ## Shift right by a bit, in place or not -/

theorem exec_extr_x {s : State} {d n m : Reg} {lsb : Nat} (h : lsb < 64) :
    exec (.extr .x d n m lsb) s = some (s.write .x d ((s.gpr n ++ s.gpr m).extractLsb' lsb 64)) := by
  simp [exec, Size.bits, h, State.read]

/-- `extr d, hi, lo, #1`: `lo / 2` with the low bit of `hi` on top. -/
theorem extr1_toNat (hi lo : BitVec 64) :
    ((hi ++ lo).extractLsb' 1 64).toNat = lo.toNat / 2 + 2 ^ 63 * (hi.toNat % 2) := by
  have hl := lo.isLt
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega_using []

/-- After `j` words of `shrBody` from `s₀`: `2 O_j + X_0 % 2 = X_j + 2^(64 j) (X_j' % 2)`
for the word `X_j'` (word `j` of `X`, unchanged). -/
structure ShrInv (s₀ : State) (B : Addr) (Z eo eX : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eo + 8 * j)
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : 2 * wv t.mem B eo j + (word s₀.mem B eX).toNat % 2 =
    wv s₀.mem B eX j + 2 ^ (64 * j) * ((word s₀.mem B (eX + 8 * j)).toNat % 2)

theorem shrStep_ok {s₀ : State} {B : Addr} {Z w eo eX : Nat}
    (ho : eo + 8 * w ≤ Z) (hX : eX + 8 * (w + 1) ≤ Z) (sX : eo = eX ∨ eX + 8 * (w + 1) ≤ eo ∨ eo + 8 * w ≤ eX)
    {j : Nat} (hj : j < w) {t : State} (hI : ShrInv s₀ B Z eo eX j t) :
    WP isa (.block (shrBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      ShrInv s₀ B Z eo eX (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x16, .x17] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eo + 8 * j))
        ((word t.mem B (eX + 8 * j + 8) ++ word t.mem B (eX + 8 * j)).extractLsb' 1 64) ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eo + 8 * j + 8))
    (by unfold shrBody; brun [hI.x16, hI.x17, exec_extr_x, hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega_using [hX, hj]),
      hI.scr.ld (show eX + 8 * j + 8 + 8 ≤ Z by omega_using [hX, hj]), hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega_using [ho, hj])])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eX + 8 * j) = word s₀.mem B (eX + 8 * j) := hI.out.word (by omega_using [sX, hj]) (by omega_using [hX, hj, hn])
  have hx' : word t.mem B (eX + 8 * j + 8) = word s₀.mem B (eX + 8 * j + 8) :=
    hI.out.word (by omega_using [sX, hj]) (by omega_using [hX, hj, hn])
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [ho, hj, hn]) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [ho, hj, hn]), extr1_toNat, hx, hx']
    have hval := hI.val
    have hX := (word s₀.mem B (eX + 8 * j)).isLt
    simp only [wv]
    rw [pow64_succ, show eX + 8 * (j + 1) = eX + 8 * j + 8 by omega_using []]
    have : (word s₀.mem B (eX + 8 * j)).toNat = 2 * ((word s₀.mem B (eX + 8 * j)).toNat / 2) +
      (word s₀.mem B (eX + 8 * j)).toNat % 2 := (Nat.div_add_mod _ _).symm
    grind

/-- `countLoop .x14 shrBody` over `N` words: `2 O + X_0 % 2 = X + 2^(64 N) (X_N % 2)`
for the `N` words `X` and the word `X_N` after them; `O` may be `X`. -/
theorem shr_ok {s : State} {B : Addr} {Z N eo eX : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h17 : s.gpr .x17 = off B eo) (h14 : s.gpr .x14 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hX : eX + 8 * (N + 1) ≤ Z)
    (sX : eo = eX ∨ eX + 8 * (N + 1) ≤ eo ∨ eo + 8 * N ≤ eX) :
    WP isa (countLoop .x14 shrBody) s fun t =>
      2 * wv t.mem B eo N + (word s.mem B eX).toNat % 2 =
        wv s.mem B eX N + 2 ^ (64 * N) * ((word s.mem B (eX + 8 * N)).toNat % 2) ∧
      t.mem = t.mem ∧ Outside B eo (8 * N) s.mem t.mem ∧ Keep [.x3, .x4, .x14, .x16, .x17] s t := by
  have h0 : ShrInv s B Z eo eX 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, Outside.refl _ _ _ _, by simp [wv]⟩
  refine WP.mono (wp_countdown (N := N) (by omega_using [hN']) (by omega_using [hN]) (ShrInv s B Z eo eX)
    (fun j hj t hI _ => shrStep_ok ho hX sX hj hI) h0 h14) fun t hI => ⟨hI.val, rfl, hI.out, hI.keep⟩

/-! ## Masked swap -/

theorem cswap_x (a b : BitVec 64) (c : Bool) : a ^^^ ((a ^^^ b) &&& mask c) = if c then b else a := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem cswap_y (a b : BitVec 64) (c : Bool) : b ^^^ ((a ^^^ b) &&& mask c) = if c then a else b := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true]
    rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- After `j` words of `cswapBody` on `X` at `eX` and `Y` at `eY`. -/
structure CsInv (s₀ : State) (B : Addr) (Z eX eY : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x5, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eY + 8 * j)
  out : ∀ x, (ofs B x < eX ∨ eX + 8 * j ≤ ofs B x) → (ofs B x < eY ∨ eY + 8 * j ≤ ofs B x) → t.mem x = s₀.mem x
  vx : ∀ i < j, word t.mem B (eX + 8 * i) =
    if c then word s₀.mem B (eY + 8 * i) else word s₀.mem B (eX + 8 * i)
  vy : ∀ i < j, word t.mem B (eY + 8 * i) =
    if c then word s₀.mem B (eX + 8 * i) else word s₀.mem B (eY + 8 * i)

theorem csStep_ok {s₀ : State} {B : Addr} {Z w eX eY : Nat} {c : Bool} (h15 : s₀.gpr .x15 = mask c)
    (hX : eX + 8 * w ≤ Z) (hY : eY + 8 * w ≤ Z) (sXY : eX + 8 * w ≤ eY ∨ eY + 8 * w ≤ eX)
    {j : Nat} (hj : j < w) {t : State} (hI : CsInv s₀ B Z eX eY c j t) :
    WP isa (.block (cswapBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      CsInv s₀ B Z eX eY c (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  have hx : word t.mem B (eX + 8 * j) = word s₀.mem B (eX + 8 * j) :=
    Mem.readW_congr fun b hb => hI.out _ (by rw [ofs_off B (by omega_using [hX, hj, hn, hb])]; omega_using [])
      (by rw [ofs_off B (by omega_using [hX, hj, hn, hb])]; omega_using [sXY, hj, hb])
  have hy : word t.mem B (eY + 8 * j) = word s₀.mem B (eY + 8 * j) :=
    Mem.readW_congr fun b hb => hI.out _ (by rw [ofs_off B (by omega_using [hY, hj, hn, hb])]; omega_using [sXY, hj, hb])
      (by rw [ofs_off B (by omega_using [hY, hj, hn, hb])]; omega_using [])
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x16, .x17] (Q := fun t₁ => t₁.mem =
      (t.mem.writeW (off B (eX + 8 * j)) (if c then word s₀.mem B (eY + 8 * j) else word s₀.mem B (eX + 8 * j))).writeW
        (off B (eY + 8 * j)) (if c then word s₀.mem B (eX + 8 * j) else word s₀.mem B (eY + 8 * j)) ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eY + 8 * j + 8)) (by
      unfold cswapBody
      brun [hI.x16, hI.x17, t15, hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega_using [hX, hj]),
        hI.scr.ld (show eY + 8 * j + 8 ≤ Z by omega_using [hY, hj]), hI.scr.st (show eX + 8 * j + 8 ≤ Z by omega_using [hX, hj]),
        hI.scr.st (show eY + 8 * j + 8 ≤ Z by omega_using [hY, hj]), hx, hy, cswap_x, cswap_y])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have o1 := writeW_outside t.mem B (if c then word s₀.mem B (eY + 8 * j) else word s₀.mem B (eX + 8 * j))
    (d := eX + 8 * j) (by omega_using [hX, hj, hn])
  have o2 := writeW_outside (t.mem.writeW (off B (eX + 8 * j))
    (if c then word s₀.mem B (eY + 8 * j) else word s₀.mem B (eX + 8 * j))) B
    (if c then word s₀.mem B (eX + 8 * j) else word s₀.mem B (eY + 8 * j)) (d := eY + 8 * j) (by omega_using [hY, hj, hn])
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_, ?_, ?_⟩
  · intro x h1 h2
    rw [hm', hm, o2 x (by omega_using [h2]), o1 x (by omega_using [h1])]
    exact hI.out x (by omega_using [h1]) (by omega_using [h2])
  · intro i hi
    rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [o2.word (by omega_arith) (by omega_arith), o1.word (by omega_arith) (by omega_arith)]; exact hI.vx i hi
    · rw [o2.word (by omega_using [sXY, hj]) (by omega_using [hX, hn, hj]), word_writeW_self]
  · intro i hi
    rw [hm', hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [o2.word (by omega_arith) (by omega_arith), o1.word (by omega_arith) (by omega_arith)]; exact hI.vy i hi
    · rw [word_writeW_self]

/-- `countLoop .x14 cswapBody` over `N` words: `[x16]` and `[x17]` swapped
if `c`. -/
theorem cswap_ok {s : State} {B : Addr} {Z N eX eY : Nat} {c : Bool} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h17 : s.gpr .x17 = off B eY) (h15 : s.gpr .x15 = mask c)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 N) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hX : eX + 8 * N ≤ Z)
    (hY : eY + 8 * N ≤ Z) (sXY : eX + 8 * N ≤ eY ∨ eY + 8 * N ≤ eX) :
    WP isa (countLoop .x14 cswapBody) s fun t =>
      wv t.mem B eX N = (if c then wv s.mem B eY N else wv s.mem B eX N) ∧
      wv t.mem B eY N = (if c then wv s.mem B eX N else wv s.mem B eY N) ∧
      Frm B [(eX, 8 * N), (eY, 8 * N)] s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x14, .x16, .x17] s t := by
  have h0 : CsInv s B Z eX eY c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, fun _ _ _ => rfl, fun i hi => absurd hi (by omega_using []),
      fun i hi => absurd hi (by omega_using [])⟩
  refine WP.mono (wp_countdown (N := N) (by omega_using [hN']) (by omega_using [hN]) (CsInv s B Z eX eY c)
    (fun j hj t hI _ => csStep_ok h15 hX hY sXY hj hI) h0 h14) fun t hI => ?_
  refine ⟨?_, ?_, fun x hx => hI.out x (hx (eX, 8 * N) (by simp)) (hx (eY, 8 * N) (by simp)), hI.keep⟩
  · cases c
    · exact wv_congr2 fun i hi => by simpa using hI.vx i hi
    · exact wv_congr2 fun i hi => by simpa using hI.vx i hi
  · cases c
    · exact wv_congr2 fun i hi => by simpa using hI.vy i hi
    · exact wv_congr2 fun i hi => by simpa using hI.vy i hi

/-! ## The `OR` of the words of an `XOR` -/

theorem xor_eq_zero (a b : BitVec 64) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· ^^^ b) h
    simpa [BitVec.xor_assoc, BitVec.xor_self] using this
  · rintro rfl; exact BitVec.xor_self

theorem or_eq_zero (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      have := congrArg (fun x => x.getLsbD i) h <;> simp_all
  · rintro ⟨rfl, rfl⟩; rfl

/-- After `j` words of `xorBody`: `x9 = 0` iff `x9` was and the first `j`
words agree. -/
structure XorInv (s₀ : State) (B : Addr) (Z eX eY : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x4, .x9, .x14, .x16, .x17] s₀ t
  mem : t.mem = s₀.mem
  c : t.c = s₀.c
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eY + 8 * j)
  val : t.gpr .x9 = 0 ↔ s₀.gpr .x9 = 0 ∧ wv s₀.mem B eX j = wv s₀.mem B eY j

theorem xorStep_ok {s₀ : State} {B : Addr} {Z w eX eY : Nat} (hX : eX + 8 * w ≤ Z) (hY : eY + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : XorInv s₀ B Z eX eY j t) :
    WP isa (.block (xorBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      XorInv s₀ B Z eX eY (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x9, .x16, .x17] (Q := fun t₁ => t₁.mem = t.mem ∧ t₁.c = t.c ∧
      t₁.gpr .x9 = t.gpr .x9 ||| (word t.mem B (eX + 8 * j) ^^^ word t.mem B (eY + 8 * j)) ∧
      t₁.gpr .x16 = off B (eX + 8 * j + 8) ∧ t₁.gpr .x17 = off B (eY + 8 * j + 8))
    (by unfold xorBody; brun [hI.x16, hI.x17, hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega_using [hX, hj]),
      hI.scr.ld (show eY + 8 * j + 8 ≤ Z by omega_using [hY, hj])]) (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨hm, hc, h9, h16, h17⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [hm', hm, hI.mem], by rw [hc', hc, hI.c], by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc], ?_⟩
  rw [k'.gpr .x9 (by decide), h9, or_eq_zero, hI.val, xor_eq_zero, hI.mem]
  have hlx := wv_lt s₀.mem B eX j
  have hly := wv_lt s₀.mem B eY j
  simp only [wv]
  constructor
  · rintro ⟨⟨h0, he⟩, hw⟩; exact ⟨h0, by rw [he, hw]⟩
  · rintro ⟨h0, he⟩
    have hw : word s₀.mem B (eX + 8 * j) = word s₀.mem B (eY + 8 * j) := by
      apply BitVec.eq_of_toNat_eq
      have := congrArg (· / 2 ^ (64 * j)) he
      rwa [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hlx, Nat.div_eq_of_lt hly, Nat.zero_add, Nat.zero_add] at this
    refine ⟨⟨h0, ?_⟩, hw⟩
    rw [hw] at he; omega_using [he]

/-- `countLoop .x14 xorBody` over `N` words: `x9 = 0` at the end iff it was
and the numbers agree. -/
theorem xor_ok {s : State} {B : Addr} {Z N eX eY : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h17 : s.gpr .x17 = off B eY) (h14 : s.gpr .x14 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hX : eX + 8 * N ≤ Z) (hY : eY + 8 * N ≤ Z) :
    WP isa (countLoop .x14 xorBody) s fun t =>
      (t.gpr .x9 = 0 ↔ s.gpr .x9 = 0 ∧ wv s.mem B eX N = wv s.mem B eY N) ∧ t.mem = s.mem ∧ t.c = s.c ∧
      Keep [.x3, .x4, .x9, .x14, .x16, .x17] s t := by
  have h0 : XorInv s B Z eX eY 0 s :=
    ⟨hs, Keep.refl _ _, rfl, rfl, by rw [h16]; rfl, by rw [h17]; rfl, by simp [wv]⟩
  refine WP.mono (wp_countdown (N := N) (by omega_using [hN']) (by omega_using [hN]) (XorInv s B Z eX eY)
    (fun j hj t hI _ => xorStep_ok hX hY hj hI) h0 h14) fun t hI => ⟨hI.val, hI.mem, hI.c, hI.keep⟩

end VG.Proof.Rsa.AArch64
