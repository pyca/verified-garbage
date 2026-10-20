module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Row
import VerifiedGarbage.Proof.Framework.Omega

/-! # The straight-line blocks of a row of the run-time width multiplication

`loadA`: the multiplier `a_i` from `ws + a + 4 i`, for `ebp` at word `i` of
the accumulator; `redDigit`: `q = t₀ (-M⁻¹) mod 2³²` from the window's low
word; `rowEnd`: `ebp` up a word and ZF at the last row.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

theorem accOff_eq : accOff = 52 := rfl
theorem multOff_eq : multOff = 20 := rfl

/-- `[edi + multOff] = a_i`. -/
theorem loadA_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    (hA0 : (A 0).toNat = W.toNat) {S a i : Nat} (hA7 : (A 7).toNat = a)
    (hedi : PtrAt s W .edi S) (hebp : PtrAt s W .ebp (S + accOff + 4 * i))
    (ha₁ : a + 4 * i + 4 ≤ L) (hacc : S + accOff + 4 * i < L) :
    WP isa (.block loadA) s fun u =>
      u.mem = s.mem.writeW (off W (S + multOff)) (s.mem.readW (off W (a + 4 * i)) 32) ∧
      Keeps [.eax, .edx] s u := by
  have hn := hw.nowrap
  have := accOff_eq
  have := multOff_eq
  simp only [loadA]
  refine wp_movS rfl fun s₀ u₀ _ => ?_
  refine wp_subS rfl fun s₁ u₁ _ => ?_
  refine wp_subS rfl fun s₂ u₂ _ => ?_
  have ha₂ : Args s₂ W L A := ((ha.of_upd u₀ (by decide)).of_upd u₁ (by decide)).of_upd u₂ (by decide)
  refine wp_movS (ha₂.read 0 (by decide)) fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => ?_
  have ha₄ : Args s₄ W L A := (ha₂.of_upd u₃ (by decide)).of_upd u₄ (by decide)
  refine wp_movS (ha₄.read 7 (by decide)) fun s₅ u₅ _ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => ?_
  have K₆ : Keeps [.eax, .edx] s s₆ :=
    (((((u₀.keeps.mono (by decide)).widen u₁.keeps).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps |>.widen
      u₅.keeps).widen u₆.keeps
  have hw₆ := hw.of_keeps K₆
  -- `eax = W + a + 4 i`.
  have e₂ : (s₂.gpr .eax).toNat = 4 * i := by
    rw [u₂.gpr, u₁.gpr, u₀.gpr, u₀.other .edi (by decide)]
    simp only [BitVec.toNat_sub, hebp, hedi, BitVec.toNat_ofNat]
    have := W.isLt
    rw [Nat.mod_eq_of_lt (a := W.toNat + (S + accOff + 4 * i)) (by omega),
      Nat.mod_eq_of_lt (a := W.toNat + S) (by omega)]
    omega
  have e₆ : PtrAt s₆ W .eax (a + 4 * i) := by
    rw [PtrAt, u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide),
      BitVec.toNat_add, BitVec.toNat_add, e₂, hA0, hA7]
    omega
  refine wp_movS (readSrc_ptr hw₆ e₆ (d := 0) (by omega)) fun s₇ u₇ _ => ?_
  have hw₇ := hw₆.of_keeps u₇.keeps
  have edi₇ : PtrAt s₇ W .edi S := by
    rw [PtrAt, u₇.other _ (by decide), K₆.1 _ (by decide)]; exact hedi
  refine wp_storeS (ea_ptr hw₇ edi₇ (d := multOff) (by omega))
    (ws_write hw₇ (y := S + multOff) (n := 4) (by omega)) fun s₈ m₈ => WP.block_nil ⟨?_, ?_⟩
  · have m₆ : s₆.mem = s.mem := by
      rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₀.mem]
    rw [m₈.mem, u₇.gpr, u₇.mem, m₆, Nat.add_zero]
  · exact (K₆.widen u₇.keeps).widen (m₈.keeps [])

/-- `[edi + multOff] = t₀ · [ws + inv] mod 2³²`, for the window's low word `t₀` at `ebp = W + w`. -/
theorem redDigitRt_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    (hA0 : (A 0).toNat = W.toNat) {S inv w : Nat} (hA4 : (A 4).toNat = inv)
    (hedi : PtrAt s W .edi S) (hebp : PtrAt s W .ebp w)
    (hv : inv + 4 ≤ L) (hw₁ : w + 4 ≤ L) (hm : S + multOff + 4 ≤ L) :
    WP isa (.block Rt.redDigit) s fun u =>
      w32 u.mem W (S + multOff) = w32 s.mem W w * w32 s.mem W inv % 2 ^ 32 ∧
      Keeps [.eax, .edx] s u ∧ Outside W (S + multOff) 4 s.mem u.mem := by
  have hn := hw.nowrap
  simp only [Rt.redDigit]
  refine WP.block_append (WP.mono (ptr_ok ha (r := .edx) (t := .eax) (i := 4) (by decide) (by decide) (by decide))
    fun s₁ ⟨e₁, _, m₁, K₁⟩ => ?_)
  have hw₁' := hw.of_keeps K₁
  have edx₁ : PtrAt s₁ W .edx inv := by rw [PtrAt, e₁, BitVec.toNat_add, hA0, hA4]
  refine wp_movS (readSrc_ptr hw₁' edx₁ (d := 0) (by omega)) fun s₂ u₂ _ => ?_
  have hw₂ := hw₁'.of_keeps u₂.keeps
  have ebp₂ : PtrAt s₂ W .ebp w := by rw [PtrAt, u₂.other _ (by decide), K₁.1 _ (by decide)]; exact hebp
  refine wp_movS (readSrc_ptr hw₂ ebp₂ (d := 0) (by omega)) fun s₃ u₃ _ => ?_
  refine wp_mul fun s₄ m₄ => ?_
  have K₄ : Keeps [.eax, .edx] s s₄ := (((K₁.widen u₂.keeps).widen u₃.keeps).widen m₄.keeps).mono (by decide)
  have hw₄ := hw.of_keeps K₄
  have edi₄ : PtrAt s₄ W .edi S := by rw [PtrAt, K₄.1 _ (by decide)]; exact hedi
  refine wp_storeS (ea_ptr hw₄ edi₄ (d := multOff) (by omega)) (ws_write hw₄ (y := S + multOff) (n := 4) (by omega))
    fun s₅ m₅ => WP.block_nil ⟨?_, K₄.widen (m₅.keeps []), ?_⟩
  · rw [m₅.mem, w32_write_self, m₄.eax, u₃.gpr, u₃.other .edx (by decide), u₂.gpr, u₂.mem, m₁,
      BitVec.toNat_ofNat, Nat.add_zero, Nat.add_zero]
  · rw [m₅.mem, m₄.mem, u₃.mem, u₂.mem, m₁]; exact writeW32_outside _ _ _ (by omega)

/-- `ebp` up a word, and ZF after the last row. -/
theorem rowEnd_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {S i N : Nat} (hn : (A 2).toNat * 8 = 4 * N) (hN32 : 4 * N < 2 ^ 32)
    (hedi : PtrAt s W .edi S) (hebp : PtrAt s W .ebp (S + accOff + 4 * i)) (hi : i < N)
    (hL : S + accOff + 4 * N ≤ L) :
    WP isa (.block Rt.rowEnd) s fun u =>
      PtrAt u W .ebp (S + accOff + 4 * (i + 1)) ∧ u.zf = some (decide (i + 1 = N)) ∧
      u.mem = s.mem ∧ Keeps [.eax, .ebp] s u := by
  have hn' := hw.nowrap
  have := accOff_eq
  simp only [Rt.rowEnd, List.cons_append, List.append_assoc]
  refine wp_addS rfl fun s₁ u₁ _ => ?_
  rw [List.nil_append]
  refine WP.block_append (WP.mono (lenTimes_ok (ha.of_upd u₁ (by decide)) (r := .eax) 0)
    fun s₂ ⟨l₂, m₂, K₂⟩ => ?_)
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => ?_
  refine wp_cmpS rfl fun s₅ f₅ z₅ => WP.block_nil ?_
  have ebp₄ : (s₄.gpr .ebp).toNat = (W.toNat + (S + accOff + 4 * (i + 1))) % 2 ^ 32 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), K₂.1 _ (by decide), u₁.gpr, ptr_add hebp]
    congr 1
  have eax₄ : (s₄.gpr .eax).toNat = (W.toNat + (S + accOff + 4 * N)) % 2 ^ 32 := by
    rw [u₄.gpr, u₃.gpr, K₂.1 .edi (by decide), u₁.other _ (by decide),
      BitVec.toNat_add, BitVec.toNat_add, l₂, len_ok hn hN32, hedi]
    simp only [BitVec.toNat_ofNat]
    omega
  refine ⟨by rw [PtrAt, f₅.gpr]; exact ebp₄, ?_, by rw [f₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem], ?_⟩
  · rw [z₅]
    congr 1
    by_cases h : i + 1 = N
    · simp only [h, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, ebp₄, eax₄, h]
      simp
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro hz
      have := congrArg BitVec.toNat hz
      rw [BitVec.toNat_sub, ebp₄, eax₄] at this
      simp at this
      have := hL
      omega
  · exact ((((u₁.keeps.mono (by decide)).widen K₂).widen u₃.keeps).widen u₄.keeps).widen (f₅.keeps [])

end VG.Proof.Mont.X86.Rt
