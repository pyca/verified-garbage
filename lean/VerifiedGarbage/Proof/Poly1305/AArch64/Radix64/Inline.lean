module

public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Setup
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Reduce
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Poly1305 radix 64 on AArch64, in a caller's code

`vg_poly1305_blocks`'s parts, run in a caller's own code: one `setup`, then
blocks absorbed from any number of places (`absorb true`, and the loop of
`blocks`), then one `reduce` and `storeH`. `HInv` is the accumulator in
registers between them: from `A`, the accumulator `setup` loaded, it has
absorbed the whole blocks `X`.
-/

@[expose] public section

namespace VG.Proof.Poly1305.AArch64.Radix64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64.Radix64
open VG.Proof.Poly1305.AArch64
open VG.Spec.Poly1305 (P bytesAt leNum clamp accumulate Repr)

/-- The clamped key `R` in `x7`, `x8` and `x17`, and the accumulator in
`x4`–`x6`: from `A` (if it is less than `p`), the whole blocks `X` absorbed. -/
def HInv (R A : Nat) (X : List Byte) (s : State) : Prop :=
  Keys R s ∧ X.length % 16 = 0 ∧
    (A < P → hval s % P = Poly1305.absorbAll R A X % P ∧ Bounds s)

theorem HInv.of_regs {R A : Nat} {X : List Byte} {s s' : State} (h : HInv R A X s)
    (hr : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8, .x17], s'.gpr r = s.gpr r) : HInv R A X s' := by
  obtain ⟨hk, hx, ha⟩ := h
  refine ⟨hk.of_regs fun r hr' => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
    rcases hr' with rfl | rfl | rfl <;> simp only [reduceCtorEq, or_true, true_or]), hx, fun hA => ?_⟩
  obtain ⟨e, b⟩ := bounds_eq (s := s) (s' := s') fun r hr' => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
    rcases hr' with rfl | rfl | rfl <;> simp only [reduceCtorEq, or_true, true_or])
  obtain ⟨hv, hb⟩ := ha hA
  exact ⟨by rw [e]; exact hv, b hb⟩

/-- `setup` from the state at `x0`: the accumulator in it, with nothing yet absorbed. -/
theorem setup_hinv (s : State) (hw : sR (s.gpr .x0) ∈ s.wr) :
    WP isa (.block setup) s fun s' =>
      HInv (Rk s.mem (s.gpr .x0)) (leNum (bytesAt s.mem (s.gpr .x0) 24)) [] s' ∧
      Keeps [.x4, .x5, .x6, .x7, .x8, .x16, .x17] s s' :=
  (setup_ok s hw).mono fun _ ⟨hk, ha, k⟩ =>
    ⟨⟨hk, rfl, fun hA => by
      obtain ⟨e, b⟩ := ha hA
      exact ⟨by rw [e, Poly1305.absorbAll_nil], b⟩⟩, k⟩

/-- The value of a block of 16 bytes with the `0x01` byte appended. -/
theorem block16_value (m : Mem) (p : Addr) :
    w64 m p 0 + 2 ^ 64 * w64 m p 8 + 2 ^ 128 * true.toNat = leNum (bytesAt m p 16 ++ [0x01]) := by
  rw [Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_key]
  have h1 : leNum [(0x01 : Byte)] = 1 := rfl
  rw [h1, Bool.toNat_true, show (256 : Nat) ^ 16 = 2 ^ 128 from rfl]

/-- One block absorbed from `x1`. -/
theorem absorb_hinv (s : State) {R A : Nat} {X : List Byte} (h : HInv R A X s)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 8) 8) :
    WP isa (.block (absorb true)) s fun s' =>
      HInv R A (X ++ bytesAt s.mem (s.gpr .x1) 16) s' ∧ Keeps absorbRegs s s' := by
  obtain ⟨hk, hx, ha⟩ := h
  refine (absorb_key_ok s true hk h0 h8).mono fun s' ⟨hab, k⟩ =>
    ⟨⟨hk.of_regs fun r hr => k.1 r ?_, ?_, fun hA => ?_⟩, k⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · rw [List.length_append, Poly1305.length_bytesAt]; omega_using [hx]
  · obtain ⟨hv, hb⟩ := ha hA
    obtain ⟨hv', hb'⟩ := hab hb
    refine ⟨?_, hb'⟩
    have hb1 : 0 < (bytesAt s.mem (s.gpr .x1) 16).length := by rw [Poly1305.length_bytesAt]; decide
    have hb2 : (bytesAt s.mem (s.gpr .x1) 16).length ≤ 16 := by rw [Poly1305.length_bytesAt]
    rw [hv', show word s.mem (s.gpr .x1) 0 = w64 s.mem (s.gpr .x1) 0 from rfl,
      show word s.mem (s.gpr .x1) 8 = w64 s.mem (s.gpr .x1) 8 from rfl, block16_value, mod_step hv,
      Poly1305.absorbAll_append hx, Poly1305.absorbAll_block hb1 hb2]

theorem keeps_refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The loop of `blocks`: the `n` blocks at `x1 = p` (`x2 = n`, nonzero),
with `x1` left past them. -/
theorem loop_hinv {R A : Nat} {X : List Byte} (s₀ : State) (h : HInv R A X s₀) {p : Addr} {n : Nat}
    (hx1 : s₀.gpr .x1 = p) (hx2 : s₀.gpr .x2 = BitVec.ofNat 64 n) (hn0 : 0 < n) (hn : 16 * n < 2 ^ 64)
    (hin : ∀ d, d + 8 ≤ 16 * n → InRegions (s₀.rd ++ s₀.wr) (p + BitVec.ofNat 64 d) 8) :
    WP isa (.loop (.block (absorb true ++ VG.Impl.Poly1305.AArch64.advance)) (.nonzero .x .x2)) s₀
      fun s' => HInv R A (X ++ bytesAt s₀.mem p (16 * n)) s' ∧
        s'.gpr .x1 = p + BitVec.ofNat 64 (16 * n) ∧ Keeps (.x1 :: .x2 :: absorbRegs) s₀ s' := by
  let Inv : Nat → State → Prop := fun m s => ∃ i, m = n - i ∧ i < n ∧
    HInv R A (X ++ bytesAt s₀.mem p (16 * i)) s ∧ s.gpr .x1 = p + BitVec.ofNat 64 (16 * i) ∧
    s.gpr .x2 = BitVec.ofNat 64 (n - i) ∧ Keeps (.x1 :: .x2 :: absorbRegs) s₀ s
  have hstep : ∀ m s, Inv m s → WP isa (.block (absorb true ++ VG.Impl.Poly1305.AArch64.advance)) s
      (fun s' => (eval (.nonzero .x .x2) s' = some false ∧
        (HInv R A (X ++ bytesAt s₀.mem p (16 * n)) s' ∧ s'.gpr .x1 = p + BitVec.ofNat 64 (16 * n) ∧
          Keeps (.x1 :: .x2 :: absorbRegs) s₀ s')) ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨i, rfl, hi, hI, hx1', hx2', ks⟩
    have hrd : ∀ d, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 d) 8 := by
      intro d hd
      rw [hx1', Offset.add_add_eq _ (c := 16 * i + d) rfl, ks.2.2.1, ks.2.2.2]
      exact hin _ (by omega_using [hd, hi])
    refine WP.block_append (WP.mono (absorb_hinv s hI (hrd 0 (by decide)) (hrd 8 (by decide)))
      fun s₁ ⟨h₁, k₁⟩ => ?_)
    refine WP.mono (VG.Proof.Poly1305.AArch64.advance_ok s₁) fun s₂ ⟨a₁, a₂, k₂⟩ => ?_
    have k₂ : Keeps [.x1, .x2] s₁ s₂ := k₂
    have hI₂ : HInv R A (X ++ bytesAt s₀.mem p (16 * (i + 1))) s₂ := by
      have e : X ++ bytesAt s₀.mem p (16 * i) ++ bytesAt s.mem (s.gpr .x1) 16 =
          X ++ bytesAt s₀.mem p (16 * (i + 1)) := by
        rw [ks.2.1, hx1', List.append_assoc, show 16 * (i + 1) = 16 * i + 16 by omega_using [],
          Poly1305.bytesAt_add]
      rw [← e]
      exact h₁.of_regs fun r hr => k₂.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    have ks₂ : Keeps (.x1 :: .x2 :: absorbRegs) s₀ s₂ :=
      ((ks.trans k₁).trans k₂).mono (by decide)
    have hx1₂ : s₂.gpr .x1 = p + BitVec.ofNat 64 (16 * (i + 1)) := by
      rw [a₁, k₁.gpr' (r := .x1), hx1', Offset.add_add, Nat.mul_succ]
    have hx2₂ : s₂.gpr .x2 = BitVec.ofNat 64 (n - (i + 1)) := by
      rw [a₂, k₁.gpr' (r := .x2), hx2', Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
    have hev : eval (.nonzero .x .x2) s₂ = some (BitVec.ofNat 64 (n - (i + 1)) != 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2₂]
    by_cases hlast : i + 1 = n
    · left
      refine ⟨by rw [hev, hlast]; simp only [Nat.sub_self, BitVec.ofNat_eq_ofNat, bne_self_eq_false],
        hlast ▸ hI₂, hlast ▸ hx1₂, ks₂⟩
    · right
      have hne : n - (i + 1) ≠ 0 := by omega_using [hi, hlast]
      have h0 : BitVec.ofNat 64 (n - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hn, h'])] at h'
        exact hne h'
      exact ⟨by rw [hev]; simpa using h0, n - (i + 1), by omega_using [hi, hne],
        i + 1, rfl, by omega_using [hi, hne], hI₂, hx1₂, hx2₂, ks₂⟩
  exact WP.loop (M := isa) Inv hstep n s₀ ⟨0, by omega_using [], hn0,
    by rw [show bytesAt s₀.mem p (16 * 0) = [] by simp [bytesAt], List.append_nil]; exact h,
    by rw [hx1]; simp only [Nat.mul_zero, BitVec.add_zero],
    by rw [hx2, Nat.sub_zero], keeps_refl _ _⟩

/-- `reduce` and `storeH`: the state at `x0`, from which `setup` loaded `R`
and `A`, then represents `msg ++ X` if it represented `msg`. -/
theorem epilogue_hinv (s : State) {R A : Nat} {X : List Byte}
    (h : HInv R A X s) (hw : sR (s.gpr .x0) ∈ s.wr)
    (hRk : Rk s.mem (s.gpr .x0) = R) (hA : leNum (bytesAt s.mem (s.gpr .x0) 24) = A) :
    WP isa (.block (reduce ++ storeH)) s fun s' =>
      (∀ key msg, Repr s.mem (s.gpr .x0) key msg → Repr s'.mem (s.gpr .x0) key (msg ++ X)) ∧
      Frame [hR (s.gpr .x0), wR (s.gpr .x0)] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14] → s'.gpr r = s.gpr r := by
  obtain ⟨_, hx, ha⟩ := h
  refine WP.block_append (WP.mono (reduce_ok s) fun s₁ ⟨hr, k₁⟩ => ?_)
  have x0₁ : s₁.gpr .x0 = s.gpr .x0 := k₁.gpr'
  refine WP.mono (VG.Proof.Poly1305.AArch64.Radix64.storeH_ok s₁ (by rw [k₁.2.2.2, x0₁]; exact hw))
    fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_
  rw [x0₁, k₁.2.1] at m₂
  have hf : Frame [hR (s.gpr .x0), wR (s.gpr .x0)] s.mem s₂.mem := by
    rw [m₂]; exact storeHm_frame (Frame.refl _ _) _ _ _
  refine ⟨fun key msg hrep => ?_, hf, by rw [rd₂, k₁.2.2.1], by rw [wr₂, k₁.2.2.2],
    fun r hr' => by rw [g₂]; exact k₁.1 r hr'⟩
  have hA' : A < P := by
    have := Poly1305.accumulate_lt (clamp (leNum (key.take 16))) msg
    rw [← hrep.2.2, hA] at this
    exact this
  obtain ⟨hv₀, hb⟩ := ha hA'
  have hN := hr hb
  have hk : bytesAt s.mem (s.gpr .x0 + 24) 32 = key := hrep.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append]; omega_using [hrep.1, hx]
  · rw [← off_24, key_frame hf, off_24]; exact hk
  · rw [m₂, storeHm_acc, ← hk, ← off_24, clamp_key, hRk, Poly1305.accumulate_append hrep.1]
    have hacc : accumulate R msg = A := by
      rw [← hA, hrep.2.2, ← hk, ← off_24, clamp_key, hRk]
    rw [hacc]
    change hval s₁ = _
    rw [hN, hv₀, Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA' _)]

end VG.Proof.Poly1305.AArch64.Radix64
