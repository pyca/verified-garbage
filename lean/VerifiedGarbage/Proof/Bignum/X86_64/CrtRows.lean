import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# Multiword arithmetic on x86-64: a product by rows

`mulRows`: `acc += a b` for `a` of `w_a` words (`r11`, `r10`) and `b` of
`w_b` words (`r9`, `r12`), row `i` adding `a_i b` at word `i` of the
accumulator (`mulAddRow`), for an accumulator of `w_a + w_b + 2` words that
starts below `2^(64 (w_b + 1))` (`mulRows_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

private theorem off_step8 (B : Addr) (q : Nat) : off B q + 8 = off B (q + 8) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- After rows `0, …, i - 1`: `acc = A₀ + b (a mod 2^(64 i))`. -/
structure MRInv (s₀ : State) (B : Addr) (Z ea eb eA wa wb : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rcx, .rdx, .rbp, .r14, .r13, .r8] s₀ t
  r13 : t.gpr .r13 = BitVec.ofNat 64 i
  r8 : t.gpr .r8 = off B (eA + 8 * i)
  out : Outside B eA (8 * (wa + wb + 2)) s₀.mem t.mem
  val : wv t.mem B eA (wa + wb + 2) = wv s₀.mem B eA (wa + wb + 2) + wv s₀.mem B eb wb * wv s₀.mem B ea i

/-- The accumulator's words as the words below `i`, the window of `k` words
at `i`, and the rest. -/
theorem wv_split3 (m : Mem) (B : Addr) (d i k L : Nat) (h : i + k ≤ L) :
    wv m B d L = wv m B d i + 2 ^ (64 * i) * (wv m B (d + 8 * i) k +
      2 ^ (64 * k) * wv m B (d + 8 * i + 8 * k) (L - i - k)) := by
  obtain ⟨r, rfl⟩ : ∃ r, L = i + (k + r) := ⟨L - i - k, by omega⟩
  rw [wv_add, wv_add, show i + (k + r) - i - k = r by omega, Nat.add_assoc d]

theorem mrStep_ok {s₀ : State} {B : Addr} {Z ea eb eA wa wb : Nat} (hs : Scr s₀ B Z)
    (h11 : s₀.gpr .r11 = off B ea) (h9 : s₀.gpr .r9 = off B eb) (h10 : s₀.gpr .r10 = BitVec.ofNat 64 wa)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 wb) (hwb : 1 ≤ wb) (hw : wa + wb < 2 ^ 30)
    (hA : eA + 8 * (wa + wb + 2) ≤ Z) (ha : ea + 8 * wa ≤ Z) (hb : eb + 8 * wb ≤ Z)
    (sa : ea + 8 * wa ≤ eA ∨ eA + 8 * (wa + wb + 2) ≤ ea) (sb : eb + 8 * wb ≤ eA ∨ eA + 8 * (wa + wb + 2) ≤ eb)
    (h0 : wv s₀.mem B eA (wa + wb + 2) < 2 ^ (64 * (wb + 1)))
    {i : Nat} (hi : i < wa) {t : State} (hI : MRInv s₀ B Z ea eb eA wa wb i t) :
    WP isa (.seq (.block [.mov .rcx (.mem (ix .r11 .r13))])
      (.seq mulAddRow (.block [.alu .add .r8 (.imm 8), .alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r10)]))) t
      fun t' => t'.zf = some (decide (i + 1 = wa)) ∧ MRInv s₀ B Z ea eb eA wa wb (i + 1) t' := by
  have hn := hs.nowrap
  have hk := hI.keep
  have t11 : t.gpr .r11 = off B ea := (hk.gpr (by decide)).trans h11
  have t9 : t.gpr .r9 = off B eb := (hk.gpr (by decide)).trans h9
  have t10 : t.gpr .r10 = BitVec.ofNat 64 wa := (hk.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 wb := (hk.gpr (by decide)).trans h12
  -- `rcx := a_i`.
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t₁ => t₁.gpr .rcx = word t.mem B (ea + 8 * i) ∧
      t₁.mem = t.mem) (by xrun [State.ea, ix, addr0 t11 hI.r13, hI.scr.ld (show ea + 8 * i + 8 ≤ Z by omega)]) rfl)
    fun t₁ ⟨⟨hcx, hm₁⟩, k₁⟩ => ?_)
  have hai : word t.mem B (ea + 8 * i) = word s₀.mem B (ea + 8 * i) := hI.out.word (by omega) (by omega)
  have fb : wv t.mem B eb wb = wv s₀.mem B eb wb := hI.out.wv (by omega) (by omega)
  -- The window and the rest of the accumulator.
  have sp := wv_split3 t.mem B eA i (wb + 2) (wa + wb + 2) (by omega)
  have hval := hI.val
  have hW : wv t.mem B (eA + 8 * i) (wb + 2) + (word s₀.mem B (ea + 8 * i)).toNat * wv s₀.mem B eb wb <
      2 ^ (64 * (wb + 2)) := by
    have hbw := wv_lt s₀.mem B eb wb
    have hai' := (word s₀.mem B (ea + 8 * i)).isLt
    have hab : (word s₀.mem B (ea + 8 * i)).toNat * wv s₀.mem B eb wb ≤ (2 ^ 64 - 1) * 2 ^ (64 * wb) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hai2 := wv_lt s₀.mem B ea i
    have hprod : wv s₀.mem B eb wb * wv s₀.mem B ea i ≤ 2 ^ (64 * wb) * 2 ^ (64 * i) :=
      Nat.mul_le_mul (by omega) (by omega)
    -- `2^(64 i) W ≤ acc < 2^(64 (wb + 1)) + 2^(64 (wb + i))`.
    have hle : 2 ^ (64 * i) * wv t.mem B (eA + 8 * i) (wb + 2) ≤ wv t.mem B eA (wa + wb + 2) := by
      rw [sp]; have := Nat.mul_le_mul_left (2 ^ (64 * i)) (Nat.le_add_right (wv t.mem B (eA + 8 * i) (wb + 2))
        (2 ^ (64 * (wb + 2)) * wv t.mem B (eA + 8 * i + 8 * (wb + 2)) (wa + wb + 2 - i - (wb + 2))))
      omega
    have e1 : 2 ^ (64 * (wb + 2)) = 2 ^ (64 * wb) * 2 ^ 128 := by
      rw [show 64 * (wb + 2) = 64 * wb + 128 by omega, Nat.pow_add]
    have e2 : 2 ^ (64 * (wb + 1)) = 2 ^ (64 * wb) * 2 ^ 64 := by
      rw [show 64 * (wb + 1) = 64 * wb + 64 by omega, Nat.pow_add]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul] at hle
      rw [show wv s₀.mem B ea 0 = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hval
      rw [e1]; rw [e2] at h0
      have : 2 ^ (64 * wb) * 2 ^ 64 + (2 ^ 64 - 1) * 2 ^ (64 * wb) ≤ 2 ^ (64 * wb) * 2 ^ 128 := by
        rw [Nat.mul_comm (2 ^ 64 - 1), ← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by decide)
      omega
    · -- `W < 2^(64 wb + 1)`.
      have hpi : 2 ^ (64 * (wb + 1)) ≤ 2 ^ (64 * wb) * 2 ^ (64 * i) := by
        rw [e2]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
      have hWlt : 2 ^ (64 * i) * wv t.mem B (eA + 8 * i) (wb + 2) < 2 ^ (64 * i) * (2 * 2 ^ (64 * wb)) := by
        have : 2 ^ (64 * i) * (2 * 2 ^ (64 * wb)) = 2 ^ (64 * wb) * 2 ^ (64 * i) + 2 ^ (64 * wb) * 2 ^ (64 * i) := by
          grind
        omega
      have hW2 := Nat.lt_of_mul_lt_mul_left hWlt
      rw [e1]
      have : 2 * 2 ^ (64 * wb) + (2 ^ 64 - 1) * 2 ^ (64 * wb) ≤ 2 ^ (64 * wb) * 2 ^ 128 := by
        rw [Nat.mul_comm (2 ^ 64 - 1), Nat.mul_comm 2, ← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by decide)
      omega
  have hs₁ := hI.scr.congr k₁.2.2
  have t₁8 : t₁.gpr .r8 = off B (eA + 8 * i) := (k₁.gpr (by decide)).trans hI.r8
  refine WP.seq (WP.mono (mulAddRow_ok hs₁ t₁8 ((k₁.gpr (by decide)).trans t9) ((k₁.gpr (by decide)).trans t12)
    hwb (by omega) (by omega) (by omega) (by omega)
    (by rw [hm₁, hcx, hai, fb]; exact hW)) fun t₂ ⟨hv₂, ho₂, k₂⟩ => ?_)
  rw [hm₁, hcx, hai, fb] at hv₂
  rw [hm₁] at ho₂
  have k12 := k₁.trans k₂
  have t₂13 : t₂.gpr .r13 = BitVec.ofNat 64 i := (k12.gpr (by decide)).trans hI.r13
  have t₂8 : t₂.gpr .r8 = off B (eA + 8 * i) := (k₂.gpr (by decide)).trans t₁8
  have t₂10 : t₂.gpr .r10 = BitVec.ofNat 64 wa := (k12.gpr (by decide)).trans t10
  have a8 : off B (eA + 8 * i) + 8 = off B (eA + 8 * (i + 1)) := by
    rw [show eA + 8 * (i + 1) = eA + 8 * i + 8 by omega, off_step8]
  refine WP.mono (WP.keep [.r8, .r13] (Q := fun t' => t'.gpr .r8 = off B (eA + 8 * (i + 1)) ∧
      t'.gpr .r13 = BitVec.ofNat 64 (i + 1) ∧ t'.zf = some (decide (i + 1 = wa)) ∧ t'.mem = t₂.mem)
    (by xrun [t₂8, t₂13, t₂10, ofNat_add_one, ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega) (show wa < 2 ^ 64 by omega), a8]) rfl)
    fun t' ⟨⟨h8', h13', hz, hm'⟩, k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr ((k12.trans k').2.2), ((hk.trans k12).trans k').mono (by simp), h13', h8', ?_, ?_⟩
  · rw [hm']
    exact hI.out.trans (ho₂.mono (by omega) (by omega))
  · -- The low words and the rest are as before.
    have sp' := wv_split3 t₂.mem B eA i (wb + 2) (wa + wb + 2) (by omega)
    have lo : wv t₂.mem B eA i = wv t.mem B eA i := ho₂.wv (Or.inl (by omega)) (by omega)
    have hi' : wv t₂.mem B (eA + 8 * i + 8 * (wb + 2)) (wa + wb + 2 - i - (wb + 2)) =
        wv t.mem B (eA + 8 * i + 8 * (wb + 2)) (wa + wb + 2 - i - (wb + 2)) :=
      ho₂.wv (Or.inr (by omega)) (by omega)
    rw [hm', sp', lo, hi', hv₂]
    have e : wv s₀.mem B ea (i + 1) = wv s₀.mem B ea i + 2 ^ (64 * i) * (word s₀.mem B (ea + 8 * i)).toNat := rfl
    rw [e]
    rw [sp] at hval
    grind

/-- `acc += a b`, for an accumulator of `w_a + w_b + 2` words below
`2^(64 (w_b + 1))`. -/
theorem mulRows_ok {s : State} {B : Addr} {Z ea eb eA wa wb : Nat} (hs : Scr s B Z)
    (h11 : s.gpr .r11 = off B ea) (h9 : s.gpr .r9 = off B eb) (h10 : s.gpr .r10 = BitVec.ofNat 64 wa)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 wb) (h8 : s.gpr .r8 = off B eA) (hwa : 1 ≤ wa) (hwb : 1 ≤ wb)
    (hw : wa + wb < 2 ^ 30)
    (hA : eA + 8 * (wa + wb + 2) ≤ Z) (ha : ea + 8 * wa ≤ Z) (hb : eb + 8 * wb ≤ Z)
    (sa : ea + 8 * wa ≤ eA ∨ eA + 8 * (wa + wb + 2) ≤ ea) (sb : eb + 8 * wb ≤ eA ∨ eA + 8 * (wa + wb + 2) ≤ eb)
    (h0 : wv s.mem B eA (wa + wb + 2) < 2 ^ (64 * (wb + 1))) :
    WP isa mulRows s fun t =>
      wv t.mem B eA (wa + wb + 2) = wv s.mem B eA (wa + wb + 2) + wv s.mem B ea wa * wv s.mem B eb wb ∧
      Outside B eA (8 * (wa + wb + 2)) s.mem t.mem ∧
      Keep [.rax, .rcx, .rdx, .rbp, .r14, .r13, .r8] s t := by
  have hn := hs.nowrap
  unfold mulRows
  refine WP.seq (WP.mono (WP.keep [.r13] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 0 ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨h13, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  rw [← hm₁] at h0
  refine WP.mono (wp_upto (a := 0) (N := wa) (by omega) (MRInv s₁ B Z ea eb eA wa wb)
    (fun i _ hi t hI => mrStep_ok hs₁ ((k₁.gpr (by decide)).trans h11) ((k₁.gpr (by decide)).trans h9)
      ((k₁.gpr (by decide)).trans h10) ((k₁.gpr (by decide)).trans h12) hwb hw hA ha hb sa sb h0 hi hI)
    (fun _ h => h)
    ⟨hs₁, Keep.refl _ _, h13, by rw [(k₁.gpr (by decide)).trans h8]; simp, Outside.refl _ _ _ _,
      by simp [wv]⟩) fun t hI => ?_
  have hv := hI.val
  have ho := hI.out
  rw [hm₁] at hv ho
  exact ⟨by rw [hv, Nat.mul_comm], ho, (k₁.trans hI.keep).mono (by simp)⟩

end VG.Proof.Bignum.X86_64
