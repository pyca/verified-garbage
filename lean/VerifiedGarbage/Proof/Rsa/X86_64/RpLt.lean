import VerifiedGarbage.Proof.Rsa.X86_64.RpCands

/-!
# `vg_rsa_recover_primes` on x86-64: comparing numbers

`wordLoop 0 ltBody`: the borrow of `[rbx] - [r10]` over `N` words, the mask
of `[rbx] < [r10]` in `rbp` (`lt_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

structure LtInv (s₀ : State) (B : Addr) (Z eX eY : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  mem : t.mem = s₀.mem
  val : ∃ c : Bool, ∃ d : Nat, d < 2 ^ (64 * j) ∧ t.gpr .rbp = mask c ∧
    d + wv s₀.mem B eY j = wv s₀.mem B eX j + 2 ^ (64 * j) * c.toNat

theorem ltStep_ok {s₀ : State} {B : Addr} {Z w eX eY : Nat}
    (hbx : s₀.gpr .rbx = off B eX) (h10 : s₀.gpr .r10 = off B eY) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hX : eX + 8 * w ≤ Z) (hY : eY + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State}
    (hI : LtInv s₀ B Z eX eY j t) :
    WP isa (.block (ltBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ LtInv s₀ B Z eX eY (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eX := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B eY := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, d, hd, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ t₁.mem = t.mem ∧ ∃ r : BitVec 64,
        r.toNat + (word t.mem B (eY + 8 * j)).toNat + c.toNat =
          (word t.mem B (eX + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl) fun t₁ ⟨⟨c', h₁, hm, r, hr⟩, k₁⟩ => ?_
  · unfold ltBody cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, hbp, cf_mask,
      hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eY + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, sbb_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  rw [hI.mem] at hr
  have hrl := r.isLt
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14,
    by rw [hm', hm, hI.mem], ⟨c', d + 2 ^ (64 * j) * r.toNat, ?_, (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [pow64_succ]
    have : 2 ^ (64 * j) * r.toNat ≤ 2 ^ (64 * j) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_sub, Nat.mul_one] at this
    omega
  · simp only [wv]
    rw [pow64_succ]
    grind

/-- `wordLoop 0 ltBody` over `N` words: `rbp` the mask of `[rbx] < [r10]`. -/
theorem lt_ok {s : State} {B : Addr} {Z N eX eY : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B eX) (h10 : s.gpr .r10 = off B eY) (h12 : s.gpr .r12 = BitVec.ofNat 64 N)
    (hbp : s.gpr .rbp = mask false) (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (hX : eX + 8 * N ≤ Z) (hY : eY + 8 * N ≤ Z) :
    WP isa (wordLoop 0 ltBody) s fun t =>
      t.gpr .rbp = mask (decide (wv s.mem B eX N < wv s.mem B eY N)) ∧ t.mem = s.mem ∧
      Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      LtInv s B Z eX eY 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, hm,
      ⟨false, 0, by simp, (k.gpr (by decide)).trans hbp, by simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN' (LtInv s B Z eX eY) h0
    (fun j _ hj t hI => ltStep_ok hbx h10 h12 (by omega) hX hY hj hI)) fun t hI => ?_
  obtain ⟨c, d, hd, hb, hv⟩ := hI.val
  refine ⟨?_, hI.mem, hI.keep⟩
  rw [hb]
  congr 1
  have := wv_lt s.mem B eY N
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
    exact (decide_eq_false (by omega)).symm
  · simp only [Bool.toNat_true, Nat.mul_one] at hv
    exact (decide_eq_true (by omega)).symm

end VG.Proof.Rsa.X86_64
