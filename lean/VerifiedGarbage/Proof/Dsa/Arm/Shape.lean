module

public import VerifiedGarbage.Impl.Dsa.Arm.Shape
public import VerifiedGarbage.Proof.Dsa.Arm.Body
public import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA on 32-bit ARM: the public checks of the domain's shape

The bit lengths of p and q are compared with the supported widths, a mask
each in the header's words 8 to 28 (`threeWidths_ok`), and the parities of
p and q in its word 32; their combination is the flag (`inspectQ_ok`): all
ones iff the shape is supported (`shapeValid`). The digest's prefix is its
length clamped to q's width (`digestPrefix_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and negOr_shr neg_bit32)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg dpVal)

/-- A word of the header. -/
abbrev hdr (base : Addr) (s : State) (d : Nat) : BitVec 32 := s.mem.readW (off base d) 32

theorem hdr_keep {base : Addr} {rs : List (Nat × Nat)} {s t : State} {d : Nat} (O : Outs base rs s.mem t.mem)
    (hO : ∀ r ∈ rs, r.1 + r.2 ≤ d ∨ d + 4 ≤ r.1) (hd : d + 4 ≤ 2 ^ 32) : hdr base t d = hdr base s d :=
  (Mem.readW_congr fun i hi => (O _ fun r hr => by
    have := hO r hr
    rw [ofs_off base (by omega)]
    omega).symm).symm

theorem mask32_or (p q : Prop) [Decidable p] [Decidable q] : mask32 p ||| mask32 q = mask32 (p ∨ q) := by
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [mask32, hp, hq, ite_true, ite_false, or_self, or_false, false_or] <;> decide

theorem width_iff {v bits : Nat} (hb : 0 < bits) :
    mask32 (2 ^ (bits - 1) ≤ v ∧ v < 2 ^ bits) = mask32 (Spec.Dsa.bitLength v = bits) :=
  mask32_iff (bitLength_iff_bounds hb).symm

/-- `[offset] = ` whether `[slot 0]` has `bits` bits. -/
theorem saveWidth_ok {s : State} {base : Addr} {size n bits offset : Nat} (hs : Ws s base size)
    (hz : 4960 ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) (hb : 0 < bits) (ho : 8 ≤ offset) (ho' : offset + 4 ≤ 36) :
    WP isa (Shape.saveWidth n bits offset) s fun t =>
      hdr base t offset = mask32 (Spec.Dsa.bitLength (val32 s.mem base (slot n 0) (2 * n)) = bits) ∧
      Rest (.r11 :: dclob) s t ∧ Outs base [(offset, 4), (slot n 11, 8 * n)] s.mem t.mem := by
  have nw := hs.nowrap
  have s0 := slot_lt (i := 0) hn48 (by decide)
  have s11 := slot_lt (i := 11) hn48 (by decide)
  have s011 := slot_le (n := n) (i := 0) (j := 11) (by decide)
  simp only [stride] at s011
  unfold Shape.saveWidth
  refine WP.seq (WP.mono (optionalWidth_ok hs (n := n) (a := modS n) (tmp := expS n) (bits := bits) hn
    (by simp only [modS]; omega) (by simp only [expS]; omega) (by simp only [modS]; omega)
    (by simp only [expS]; omega) (by omega) hb (by simp only [modS, expS]; omega)) fun u ⟨eu, Ru, Ou⟩ => ?_)
  have wu := hs.of_rest Ru (by decide)
  refine wp_str (by omega) (wu.ea12 (by omega)) (wu.write (by omega)) fun t m => WP.block_nil ⟨?_, Ru.trans (m.rest _), ?_⟩
  · rw [hdr, m.mem, Mem.readW_writeW_self32, eu, width_iff hb]
    rfl
  · rw [m.mem]
    exact (Outs.of_outside Ou (by simp [expS])).trans (Outs.of_outside (writeW32_outside _ _ _ (by omega)) (by simp))

theorem threeWidths_ok {s : State} {base : Addr} {size n a b c offset : Nat} (hs : Ws s base size)
    (hz : 4960 ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ho : 8 ≤ offset)
    (ho' : offset + 12 ≤ 36) :
    WP isa (Shape.threeWidths n a b c offset) s fun t =>
      hdr base t offset = mask32 (Spec.Dsa.bitLength (val32 s.mem base (slot n 0) (2 * n)) = a) ∧
      hdr base t (offset + 4) = mask32 (Spec.Dsa.bitLength (val32 s.mem base (slot n 0) (2 * n)) = b) ∧
      hdr base t (offset + 8) = mask32 (Spec.Dsa.bitLength (val32 s.mem base (slot n 0) (2 * n)) = c) ∧
      Rest (.r11 :: dclob) s t ∧ Outs base [(offset, 12), (slot n 11, 8 * n)] s.mem t.mem := by
  have nw := hs.nowrap
  have s0 := slot_lt (i := 0) hn48 (by decide)
  have s011 := slot_le (n := n) (i := 0) (j := 11) (by decide)
  have s11 := slot_lt (i := 11) hn48 (by decide)
  simp only [stride] at s011
  have sub : ∀ d, offset ≤ d → d + 4 ≤ offset + 12 → ∀ {m m' : Mem},
      Outs base [(d, 4), (slot n 11, 8 * n)] m m' → Outs base [(offset, 12), (slot n 11, 8 * n)] m m' :=
    fun d h₁ h₂ m m' O x hx => O x fun r hr => by
      have e₁ := hx (offset, 12) (by simp)
      have e₂ := hx (slot n 11, 8 * n) (by simp)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only at e₁ e₂
      rcases hr with rfl | rfl <;> simp only <;> omega
  have keep0 : ∀ {d : Nat} {m m' : Mem}, d + 4 ≤ 36 → Outs base [(d, 4), (slot n 11, 8 * n)] m m' →
      val32 m' base (slot n 0) (2 * n) = val32 m base (slot n 0) (2 * n) := fun hd O =>
    O.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  have hkeep : ∀ {d e : Nat} {m m' : Mem}, e + 4 ≤ 36 → d + 4 ≤ 36 → (e + 4 ≤ d ∨ d + 4 ≤ e) →
      Outs base [(e, 4), (slot n 11, 8 * n)] m m' → m'.readW (off base d) 32 = m.readW (off base d) 32 :=
    fun he hd hde O => (Mem.readW_congr fun i hi => (O _ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [ofs_off base (by omega)]
      rcases hr with rfl | rfl <;> simp only <;> omega).symm).symm
  unfold Shape.threeWidths
  refine WP.seq (WP.mono (saveWidth_ok hs hz hn hn48 ha (offset := offset) ho (by omega)) fun u₁ ⟨E₁, R₁, O₁⟩ => ?_)
  have w₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.mono (saveWidth_ok w₁ hz hn hn48 hb (offset := offset + 4) (by omega) (by omega))
    fun u₂ ⟨E₂, R₂, O₂⟩ => ?_)
  have w₂ := w₁.of_rest R₂ (by decide)
  refine WP.mono (saveWidth_ok w₂ hz hn hn48 hc (offset := offset + 8) (by omega) (by omega))
    fun t ⟨E₃, R₃, O₃⟩ => ⟨?_, ?_, ?_, (R₁.trans R₂).trans R₃, ((sub offset (by omega) (by omega) O₁).trans
      (sub (offset + 4) (by omega) (by omega) O₂)).trans (sub (offset + 8) (by omega) (by omega) O₃)⟩
  · rw [hdr, hkeep (by omega) (by omega) (.inr (by omega)) O₃, hkeep (by omega) (by omega) (.inr (by omega)) O₂]; exact E₁
  · rw [hdr, hkeep (by omega) (by omega) (.inr (by omega)) O₃, ← keep0 (by omega) O₁]; exact E₂
  · rw [E₃, keep0 (by omega) O₂, keep0 (by omega) O₁]

/-- Ranges each within one of others. -/
theorem Outs.within {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m')
    (h : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m m' :=
  fun x hx => O x fun r hr => by
    obtain ⟨r', hr', h₁, h₂⟩ := h r hr
    have := hx r' hr'
    omega

/-- The masks of a modulus's widths. -/
theorem loadWidths_ok {s : State} {base : Addr} {size len n a b c offset m : Nat} {modulus : Impl.Dsa.Layout.Field}
    (hs : Ws s base size) (hz : 4960 ≤ size) (w : Width len n) (R : Ready s base (.input modulus) len)
    (hm : operand base s (.input modulus) len = m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ho : 8 ≤ offset)
    (ho' : offset + 12 ≤ 36) :
    WP isa (Shape.loadWidths len modulus a b c offset) s fun t =>
      hdr base t offset = mask32 (Spec.Dsa.bitLength m = a) ∧
      hdr base t (offset + 4) = mask32 (Spec.Dsa.bitLength m = b) ∧
      hdr base t (offset + 8) = mask32 (Spec.Dsa.bitLength m = c) ∧
      val32 t.mem base (slot n 0) (2 * n) = m ∧
      Rest coreClob s t ∧ Outs base [(offset, 12), (256, 4704)] s.mem t.mem := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have nw := hs.nowrap
  have s0 := slot_lt (i := 0) n48 (by decide)
  have s11 := slot_lt (i := 11) n48 (by decide)
  have s011 := slot_le (n := n) (i := 0) (j := 11) (by decide)
  simp only [stride] at s011
  unfold Shape.loadWidths
  dsimp only
  rw [← w.n_eq]
  refine WP.seq (WP.mono (loadSlot_ok (i := 0) hs hz w (by decide) R) fun u ⟨wu, Vu, Ru, Ou⟩ => ?_)
  rw [hm] at Vu
  refine WP.mono (threeWidths_ok wu hz n0 n48 ha hb hc ho ho') fun t ⟨E₁, E₂, E₃, Rt, Ot⟩ =>
    ⟨by rw [E₁, Vu], by rw [E₂, Vu], by rw [E₃, Vu], ?_, Ru.trans (Rt.mono (by decide)), ?_⟩
  · rw [Ot.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)]
    exact Vu
  · refine (Outs.within (Outs.of_outside Ou (List.mem_singleton_self _)) ?_).trans (Outs.within Ot ?_)
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨(256, 4704), by simp, by simp only; omega, by simp only; omega⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨(offset, 12), by simp, by simp only; omega, by simp only; omega⟩
      · exact ⟨(256, 4704), by simp, by simp only; omega, by simp only; omega⟩

theorem wp_ldr12 {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t : Reg} {d : Nat}
    (hd : d < 4096) (hd' : d + 4 ≤ size) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (hdr base s d) → WP isa (.block is) s' Q) : WP isa (.block (.ldr t .r12 d :: is)) s Q :=
  wp_ldr hd (hs.ea12 (by omega)) (hs.read hd') k

theorem inspectP_ok {s : State} {base : Addr} {size pLen nP P : Nat} (hs : Ws s base size) (hz : 4960 ≤ size)
    (w : Width pLen nP) (R : Ready s base (.input .p) pLen) (hm : operand base s (.input .p) pLen = P) :
    WP isa (Shape.inspectP pLen) s fun t =>
      hdr base t 8 = mask32 (Spec.Dsa.bitLength P = 1024) ∧
      hdr base t 12 = mask32 (Spec.Dsa.bitLength P = 2048) ∧
      hdr base t 16 = mask32 (Spec.Dsa.bitLength P = 3072) ∧ (hdr base t 32).toNat % 2 = P % 2 ∧
      Rest coreClob s t ∧ Outs base [(8, 12), (32, 4), (256, 4704)] s.mem t.mem := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have nw := hs.nowrap
  have s0 := slot_lt (i := 0) n48 (by decide)
  unfold Shape.inspectP
  rw [← w.n_eq]
  refine WP.seq (WP.mono (loadWidths_ok (offset := 8) hs hz w R hm (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun u ⟨E₁, E₂, E₃, Vu, Ru, Ou⟩ => ?_)
  have wu := hs.of_rest Ru (by decide)
  simp only [Shape.saveParity]
  refine wp_ptr (d := .r10) (by decide) (by simp only [modS]; omega) fun u₁ v₁ => ?_
  have w₁ := wu.of_upd v₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (K := modS nP) (d := 0) (by rw [v₁.gpr, v₁.other .r12 (by decide)])
    (by simp only [modS]; omega)) (w₁.read (d := modS nP + 0) (n := 4) (by simp only [modS]; omega)) fun u₂ v₂ => ?_
  have w₂ := w₁.of_upd v₂ (by decide)
  refine wp_str (by decide) (w₂.ea12 (by omega)) (w₂.write (d := 32) (by omega)) fun t m => WP.block_nil ?_
  have mt : t.mem = u.mem.writeW (off base 32) (u.mem.readW (off base (slot nP 0)) 32) := by
    rw [m.mem, v₂.gpr, v₂.mem, v₁.mem, Nat.add_zero]; rfl
  have k : ∀ d, d + 4 ≤ 32 → hdr base t d = hdr base u d := fun d hd => by
    rw [hdr, hdr, mt]
    exact Mem.readW_writeW_sep (Offset.sep base (.inl hd) (by omega) (by omega)) (by decide)
  refine ⟨by rw [k 8 (by decide)]; exact E₁, by rw [k 12 (by decide)]; exact E₂, by rw [k 16 (by decide)]; exact E₃,
    ?_, Ru.trans (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (m.rest _)), ?_⟩
  · rw [hdr, mt, Mem.readW_writeW_self32, ← Vu, show 2 * nP = (2 * nP - 1) + 1 by omega, val32_parity]
  · rw [mt]
    refine (Outs.within Ou (fun r hr => ?_)).trans (Outs.of_outside (writeW32_outside _ _ _ (by omega)) (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨(8, 12), by simp, by simp only; omega, by simp only; omega⟩
    · exact ⟨(256, 4704), by simp, by simp only; omega, by simp only; omega⟩

/-- Both low bits set, as a mask. -/
theorem odd_mask (x y : BitVec 32) : 0 - (x &&& y &&& 1) = mask32 (x.toNat % 2 = 1 ∧ y.toNat % 2 = 1) := by
  have h : (x &&& y &&& 1).toNat = x.toNat % 2 &&& y.toNat % 2 := by
    have := @Nat.and_mod_two_pow x.toNat y.toNat 1
    simp only [Nat.pow_one] at this
    rw [BitVec.toNat_and, BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, this]
  have e : x &&& y &&& 1 = if x.toNat % 2 = 1 ∧ y.toNat % 2 = 1 then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [h]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> simp [hx, hy]
  rw [e]
  by_cases hb : x.toNat % 2 = 1 ∧ y.toNat % 2 = 1 <;> simp only [mask32, hb, ↓reduceIte] <;> decide

/-- The flag: a supported pair of widths, and both parities. -/
theorem combine_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    {a8 a12 a16 a20 a24 a28 a32 : Prop} [Decidable a8] [Decidable a12] [Decidable a16] [Decidable a20]
    [Decidable a24] [Decidable a28] [Decidable a32]
    (h8 : s.mem.readW (off base 8) 32 = mask32 a8) (h12 : s.mem.readW (off base 12) 32 = mask32 a12)
    (h16 : s.mem.readW (off base 16) 32 = mask32 a16) (h20 : s.mem.readW (off base 20) 32 = mask32 a20)
    (h24 : s.mem.readW (off base 24) 32 = mask32 a24) (h28 : s.mem.readW (off base 28) 32 = mask32 a28)
    (h32 : s.mem.readW (off base 32) 32 = mask32 a32) :
    WP isa (.block Shape.combine) s fun t =>
      maskW base t = mask32 ((((a8 ∧ a20) ∨ (((a24 ∨ a28) ∨ a20) ∧ a12)) ∨ (a16 ∧ a28)) ∧ a32) ∧
      Rest [.r4, .r5, .r7] s t ∧ Outside base 116 4 s.mem t.mem := by
  have nw := hs.nowrap
  have fm : Impl.Dsa.Arm.Layout.field .mask = 116 := rfl
  simp only [Shape.combine]
  refine wp_ldr12 hs (by decide) (by omega) fun s₁ u₁ => ?_
  have w₁ := hs.of_upd u₁ (by decide)
  refine wp_ldr12 w₁ (by decide) (by omega) fun s₂ u₂ => ?_
  have w₂ := w₁.of_upd u₂ (by decide)
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have w₃ := w₂.of_upd u₃ (by decide)
  refine wp_ldr12 w₃ (by decide) (by omega) fun s₄ u₄ => ?_
  have w₄ := w₃.of_upd u₄ (by decide)
  refine wp_ldr12 w₄ (by decide) (by omega) fun s₅ u₅ => ?_
  have w₅ := w₄.of_upd u₅ (by decide)
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  have w₆ := w₅.of_upd u₆ (by decide)
  refine wp_ldr12 w₆ (by decide) (by omega) fun s₆a u₆a => ?_
  have w₆a := w₆.of_upd u₆a (by decide)
  refine wp_dp (op2_reg _ _) fun s₆b u₆b => ?_
  have w₆b := w₆a.of_upd u₆b (by decide)
  refine wp_ldr12 w₆b (by decide) (by omega) fun s₇ u₇ => ?_
  have w₇ := w₆b.of_upd u₇ (by decide)
  refine wp_dp (op2_reg _ _) fun s₈ u₈ => wp_dp (op2_reg _ _) fun s₉ u₉ => ?_
  have w₉ := (w₇.of_upd u₈ (by decide)).of_upd u₉ (by decide)
  refine wp_ldr12 w₉ (by decide) (by omega) fun s₁₀ u₁₀ => ?_
  have w₁₀ := w₉.of_upd u₁₀ (by decide)
  refine wp_ldr12 w₁₀ (by decide) (by omega) fun s₁₁ u₁₁ => ?_
  have w₁₁ := w₁₀.of_upd u₁₁ (by decide)
  refine wp_dp (op2_reg _ _) fun s₁₂ u₁₂ => wp_dp (op2_reg _ _) fun s₁₃ u₁₃ => ?_
  have w₁₃ := (w₁₁.of_upd u₁₂ (by decide)).of_upd u₁₃ (by decide)
  refine wp_ldr12 w₁₃ (by decide) (by omega) fun s₁₄ u₁₄ => ?_
  have w₁₄ := w₁₃.of_upd u₁₄ (by decide)
  refine wp_dp (op2_reg _ _) fun s₁₅ u₁₅ => ?_
  have w₁₅ := w₁₄.of_upd u₁₅ (by decide)
  refine wp_str (by decide) (w₁₅.ea12 (by omega)) (w₁₅.write (d := 116) (by omega)) fun t m => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [maskW, flagW, m.mem, show Impl.Dsa.Arm.Layout.field .mask = 116 from rfl, Mem.readW_writeW_self32]
    simp only [u₁₅.get, u₁₄.get, u₁₃.get, u₁₂.get, u₁₁.get, u₁₀.get, u₉.get, u₈.get, u₇.get, u₆b.get, u₆a.get, u₆.get, u₅.get,
      u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal, hdr, u₁₃.mem, u₁₂.mem, u₁₁.mem,
      u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆b.mem, u₆a.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h8, h12, h16, h20, h24, h28,
      h32, mask32_and, mask32_or]
  · exact (((((((((((((((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
      (u₄.rest (by decide))).trans (u₅.rest (by decide))).trans (u₆.rest (by decide))).trans (u₆a.rest (by decide))).trans (u₆b.rest (by decide))).trans (u₇.rest (by decide))).trans
      (u₈.rest (by decide))).trans (u₉.rest (by decide))).trans (u₁₀.rest (by decide))).trans (u₁₁.rest (by decide))).trans
      (u₁₂.rest (by decide))).trans (u₁₃.rest (by decide))).trans (u₁₄.rest (by decide))).trans (u₁₅.rest (by decide))).trans
      (m.rest _)
  · rw [m.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆b.mem, u₆a.mem, u₆.mem, u₅.mem, u₄.mem,
      u₃.mem, u₂.mem, u₁.mem]
    exact writeW32_outside _ _ _ (by omega)

/-- `[32]` = whether `[slot 0]` and `[32]` are both odd. -/
theorem parity_ok {s : State} {base : Addr} {size n : Nat} (hs : Ws s base size) (hz : 4960 ≤ size) (hn : 0 < n)
    (hn48 : n ≤ 48) :
    WP isa (.block (Shape.parity n)) s fun t =>
      hdr base t 32 = mask32 (w32 s.mem base (slot n 0) % 2 = 1 ∧ (hdr base s 32).toNat % 2 = 1) ∧
      Rest [.r2, .r4, .r10] s t ∧ Outside base 32 4 s.mem t.mem := by
  have nw := hs.nowrap
  have s0 := slot_lt (i := 0) hn48 (by decide)
  simp only [Shape.parity]
  refine wp_ptr (d := .r10) (by decide) (by simp only [modS]; omega) fun u₁ v₁ => ?_
  have w₁ := hs.of_upd v₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (K := modS n) (d := 0) (by rw [v₁.gpr, v₁.other .r12 (by decide)])
    (by simp only [modS]; omega)) (w₁.read (d := modS n + 0) (n := 4) (by simp only [modS]; omega)) fun u₂ v₂ => ?_
  have w₂ := w₁.of_upd v₂ (by decide)
  refine wp_ldr12 w₂ (by decide) (by omega) fun u₃ v₃ => ?_
  have w₃ := w₂.of_upd v₃ (by decide)
  refine wp_dp (op2_reg _ _) fun u₄ v₄ => wp_dp (op2_imm (by decide)) fun u₅ v₅ => wp_mov (op2_imm (by decide))
    fun u₆ v₆ => wp_dp (op2_reg _ _) fun u₇ v₇ => ?_
  have w₇ := (((w₃.of_upd v₄ (by decide)).of_upd v₅ (by decide)).of_upd v₆ (by decide)).of_upd v₇ (by decide)
  refine wp_str (by decide) (w₇.ea12 (by omega)) (w₇.write (d := 32) (by omega)) fun t m => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hdr, m.mem, Mem.readW_writeW_self32]
    simp only [v₇.get, v₆.get, v₅.get, v₄.get, v₃.get, v₂.get, reduceCtorEq, ↓reduceIte, dpVal, hdr,
      v₂.mem, v₁.mem, Nat.add_zero]
    exact odd_mask _ _
  · exact ((((((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (v₃.rest (by decide))).trans
      (v₄.rest (by decide))).trans (v₅.rest (by decide))).trans ((v₆.rest (by decide)).trans (v₇.rest (by decide)))).trans
      (m.rest _)
  · rw [m.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
    exact writeW32_outside _ _ _ (by omega)

/-- The shape of a supported domain. -/
theorem shape_iff (P Q : Nat) :
    ((((Spec.Dsa.bitLength P = 1024 ∧ Spec.Dsa.bitLength Q = 160) ∨
      (((Spec.Dsa.bitLength Q = 224 ∨ Spec.Dsa.bitLength Q = 256) ∨ Spec.Dsa.bitLength Q = 160) ∧ Spec.Dsa.bitLength P = 2048)) ∨
      (Spec.Dsa.bitLength P = 3072 ∧ Spec.Dsa.bitLength Q = 256)) ∧ (Q % 2 = 1 ∧ P % 2 = 1)) ↔
      shapeValid P Q := by
  simp only [shapeValid, Spec.Dsa.supportedSizes]
  omega

theorem inspectQ_ok {s : State} {base : Addr} {size qLen nQ P Q : Nat} (hs : Ws s base size) (hz : 4960 ≤ size)
    (w : Width qLen nQ) (R : Ready s base (.input .q) qLen) (hm : operand base s (.input .q) qLen = Q)
    (h8 : hdr base s 8 = mask32 (Spec.Dsa.bitLength P = 1024))
    (h12 : hdr base s 12 = mask32 (Spec.Dsa.bitLength P = 2048))
    (h16 : hdr base s 16 = mask32 (Spec.Dsa.bitLength P = 3072)) (h32 : (hdr base s 32).toNat % 2 = P % 2) :
    WP isa (Shape.inspectQ qLen) s fun t =>
      maskW base t = mask32 (shapeValid P Q) ∧
      hdr base t 20 = mask32 (Spec.Dsa.bitLength Q = 160) ∧
      hdr base t 24 = mask32 (Spec.Dsa.bitLength Q = 224) ∧
      hdr base t 28 = mask32 (Spec.Dsa.bitLength Q = 256) ∧
      Rest coreClob s t ∧ Outs base [(20, 16), (116, 4), (256, 4704)] s.mem t.mem := by
  obtain ⟨n0, n48, hl, hl'⟩ := w.bounds
  have nw := hs.nowrap
  unfold Shape.inspectQ
  rw [← w.n_eq]
  refine WP.seq (WP.mono (loadWidths_ok (offset := 20) hs hz w R hm (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun u ⟨E₁, E₂, E₃, Vu, Ru, Ou⟩ => ?_)
  have wu := hs.of_rest Ru (by decide)
  have k : ∀ d, d + 4 ≤ 20 ∨ (32 ≤ d ∧ d + 4 ≤ 256) → hdr base u d = hdr base s d := fun d hd =>
    hdr_keep Ou (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega) (by omega)
  refine VG.Proof.X25519.Arm.WP.append (parity_ok wu hz n0 n48) fun v ⟨Pv, Rv, Ov⟩ => ?_
  have wv := wu.of_rest Rv (by decide)
  have kv : ∀ d, d + 4 ≤ 32 → hdr base v d = hdr base u d := fun d hd =>
    hdr_keep (rs := [(32, 4)]) (Outs.of_outside Ov (by simp)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; simp only; omega) (by omega)
  have par : w32 u.mem base (slot nQ 0) % 2 = Q % 2 := by
    rw [← Vu, show 2 * nQ = (2 * nQ - 1) + 1 by omega, val32_parity]
  rw [k 32 (by omega), par, h32] at Pv
  refine WP.mono (combine_ok wv (by omega) (a8 := Spec.Dsa.bitLength P = 1024)
    (a12 := Spec.Dsa.bitLength P = 2048) (a16 := Spec.Dsa.bitLength P = 3072)
    (a20 := Spec.Dsa.bitLength Q = 160) (a24 := Spec.Dsa.bitLength Q = 224) (a28 := Spec.Dsa.bitLength Q = 256)
    (a32 := Q % 2 = 1 ∧ P % 2 = 1) (by rw [← h8, ← k 8 (by omega)]; exact kv 8 (by omega))
    (by rw [← h12, ← k 12 (by omega)]; exact kv 12 (by omega))
    (by rw [← h16, ← k 16 (by omega)]; exact kv 16 (by omega))
    (by rw [← E₁]; exact kv 20 (by omega)) (by rw [← E₂]; exact kv 24 (by omega))
    (by rw [← E₃]; exact kv 28 (by omega)) Pv) fun t ⟨Mt, Rt, Ot⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Mt]; exact mask32_iff (shape_iff P Q)
  · rw [← E₁, ← kv 20 (by omega)]
    exact hdr_keep (rs := [(116, 4)]) (Outs.of_outside Ot (by simp)) (by simp) (by omega)
  · rw [← E₂, ← kv 24 (by omega)]
    exact hdr_keep (rs := [(116, 4)]) (Outs.of_outside Ot (by simp)) (by simp) (by omega)
  · rw [← E₃, ← kv 28 (by omega)]
    exact hdr_keep (rs := [(116, 4)]) (Outs.of_outside Ot (by simp)) (by simp) (by omega)
  · exact Ru.trans ((Rv.mono (by decide)).trans (Rt.mono (by decide)))
  · refine ((Outs.within Ou ?_).trans (Outs.within (Outs.of_outside Ov (List.mem_singleton_self _)) ?_)).trans
      (Outs.within (Outs.of_outside Ot (List.mem_singleton_self _)) ?_)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨(20, 16), by simp, by simp only; omega, by simp only; omega⟩
      · exact ⟨(256, 4704), by simp, by simp only; omega, by simp only; omega⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨(20, 16), by simp, by simp only; omega, by simp only; omega⟩
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨(116, 4), by simp, by simp only; omega, by simp only; omega⟩

/-- The byte width of a supported q, else zero. -/
def qWidth (Q : Nat) : Nat :=
  if Spec.Dsa.bitLength Q = 160 then 20 else if Spec.Dsa.bitLength Q = 224 then 28
  else if Spec.Dsa.bitLength Q = 256 then 32 else 0

theorem qWidth_le (Q : Nat) : qWidth Q ≤ 32 := by
  unfold qWidth; split <;> (try split) <;> (try split) <;> omega

theorem prefixWidth_ok {s : State} {base : Addr} {size Q : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    (h20 : hdr base s 20 = mask32 (Spec.Dsa.bitLength Q = 160))
    (h24 : hdr base s 24 = mask32 (Spec.Dsa.bitLength Q = 224))
    (h28 : hdr base s 28 = mask32 (Spec.Dsa.bitLength Q = 256)) :
    WP isa (.block Shape.prefixWidth) s fun t =>
      t.gpr .r2 = BitVec.ofNat 32 (qWidth Q) ∧ Rest [.r2, .r4] s t ∧ t.mem = s.mem := by
  simp only [Shape.prefixWidth]
  refine wp_ldr12 hs (by decide) (by omega) fun s₁ u₁ => wp_dp (op2_imm (by decide)) fun s₂ u₂ => ?_
  have w₂ := (hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  refine wp_ldr12 w₂ (by decide) (by omega) fun s₃ u₃ => wp_dp (op2_imm (by decide)) fun s₄ u₄ =>
    wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have w₅ := ((w₂.of_upd u₃ (by decide)).of_upd u₄ (by decide)).of_upd u₅ (by decide)
  refine wp_ldr12 w₅ (by decide) (by omega) fun s₆ u₆ => wp_dp (op2_imm (by decide)) fun s₇ u₇ =>
    wp_dp (op2_reg _ _) fun t u₈ => WP.block_nil ⟨?_, ?_, ?_⟩
  · simp only [u₈.get, u₇.get, u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal,
      hdr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    simp only [hdr] at h20 h24 h28
    rw [h20, h24, h28]
    unfold qWidth
    rcases (by omega : Spec.Dsa.bitLength Q = 160 ∨ Spec.Dsa.bitLength Q = 224 ∨ Spec.Dsa.bitLength Q = 256 ∨
      (Spec.Dsa.bitLength Q ≠ 160 ∧ Spec.Dsa.bitLength Q ≠ 224 ∧ Spec.Dsa.bitLength Q ≠ 256)) with
      h | h | h | ⟨h₁, h₂, h₃⟩ <;> simp [mask32, *] <;> decide
  · exact (((((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
      (u₄.rest (by decide))).trans (u₅.rest (by decide))).trans (u₆.rest (by decide))).trans
      (u₇.rest (by decide))).trans (u₈.rest (by decide))
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

/-- A word selected by a mask: `w ^ ((d ^ w) & m)`. -/
theorem select_min {d w : BitVec 32} (b : Bool) :
    (w ^^^ ((d ^^^ w) &&& (if b then BitVec.allOnes 32 else 0))) = if b then d else w := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (0 : BitVec 32) = 0#32 from rfl, BitVec.and_zero, BitVec.xor_zero]
  · simp only [↓reduceIte, BitVec.and_allOnes]
    rw [BitVec.xor_comm d w, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem digestClamp_ok {s : State} {base : Addr} {size W : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    (hw : s.gpr .r2 = BitVec.ofNat 32 W) (hW : W < 2 ^ 32) :
    WP isa (.block Shape.digestClamp) s fun t =>
      (hdr base t 112).toNat = min (hdr base s 108).toNat W ∧
      Rest [.r0, .r2, .r3, .r4, .r5, .r6, .r7] s t ∧ Outside base 112 4 s.mem t.mem := by
  have nw := hs.nowrap
  have fdl : Impl.Dsa.Arm.Layout.field .digestLen = 108 := rfl
  have fdp : Impl.Dsa.Arm.Layout.field .digestPrefixLen = 112 := rfl
  simp only [Shape.digestClamp, List.cons_append, List.append_assoc, List.nil_append]
  refine wp_ldr12 hs (by decide) (by omega) fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_mov (op2_imm (by decide))
    fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  have dl : (s₄.gpr .r7).toNat = (hdr base s 108).toNat := by
    rw [u₄.other .r7 (by decide), u₃.other .r7 (by decide), u₂.other .r7 (by decide), u₁.gpr, fdl]
  have wv : (s₄.gpr .r5).toNat = W := by
    rw [u₄.gpr, u₃.other .r2 (by decide), u₂.other .r2 (by decide), u₁.other .r2 (by decide), hw,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW]
  have r6 : s₄.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₄.other .r6 (by decide), u₃.other .r6 (by decide), u₂.gpr]
  have r3 : (s₄.gpr .r3).toNat = 1 := by rw [u₄.other .r3 (by decide), u₃.gpr]; rfl
  refine borrowDigit_ok (h := 0) (by decide) r6 (by omega) fun s₅ X₅ C₅ R₅ M₅ => ?_
  refine borrowDigit_ok (h := 1) (by decide) (by rw [R₅.gpr _ (by decide)]; exact r6)
    (by have := hdig_lt (s₄.gpr .r7).toNat 0; rw [C₅, X₅]; omega) fun s₆ X₆ C₆ R₆ M₆ => ?_
  rw [R₅.gpr .r7 (by decide), R₅.gpr .r5 (by decide), dl, wv] at X₆
  rw [dl, wv] at X₅
  obtain ⟨hb, hc⟩ := borrowWord (u := s₄) dl wv (by omega) (by rw [dl, wv]; exact X₅) C₅ X₆ C₆
    (BitVec.isLt _) (by omega)
  rw [r3] at hb
  have carry : s₆.gpr .r3 = if W ≤ (hdr base s 108).toNat then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    by_cases h : W ≤ (hdr base s 108).toNat
    · rw [ite_eq_left h]; show _ = 1; omega
    · rw [ite_eq_right h]; show _ = 0; omega
  refine wp_dp (op2_imm (by decide)) fun s₇ u₇ => wp_dp (op2_reg _ _) fun s₈ u₈ => wp_dp (op2_reg _ _) fun s₉ u₉ =>
    wp_dp (op2_reg _ _) fun s₁₀ u₁₀ => ?_
  have w₁₀ := ((((((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)).of_upd u₄ (by decide)).of_rest
    R₅ (by decide)).of_rest R₆ (by decide) |>.of_upd u₇ (by decide) |>.of_upd u₈ (by decide) |>.of_upd u₉ (by decide)
    |>.of_upd u₁₀ (by decide))
  refine wp_str (by decide) (w₁₀.ea12 (by omega)) (w₁₀.write (d := 112) (by omega)) fun t m => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hdr, m.mem, fdp, Mem.readW_writeW_self32]
    have m3 : s₇.gpr .r3 = if decide ((hdr base s 108).toNat < W) then BitVec.allOnes 32 else 0 := by
      rw [u₇.gpr, dpVal, carry]
      by_cases h : W ≤ (hdr base s 108).toNat
      · rw [ite_eq_left h, decide_eq_false (by omega)]; rfl
      · rw [ite_eq_right h, decide_eq_true (by omega)]; rfl
    have r2₆ : s₆.gpr .r2 = BitVec.ofNat 32 W := by
      rw [R₆.gpr .r2 (by decide), R₅.gpr .r2 (by decide), u₄.other .r2 (by decide), u₃.other .r2 (by decide),
        u₂.other .r2 (by decide), u₁.other .r2 (by decide), hw]
    have r7₆ : s₆.gpr .r7 = hdr base s 108 := by
      rw [R₆.gpr .r7 (by decide), R₅.gpr .r7 (by decide), u₄.other .r7 (by decide), u₃.other .r7 (by decide),
        u₂.other .r7 (by decide), u₁.gpr, fdl]
    rw [u₁₀.gpr, dpVal, u₉.other .r2 (by decide), u₈.other .r2 (by decide), u₇.other .r2 (by decide), u₉.gpr, dpVal,
      u₈.gpr, dpVal, u₈.other .r3 (by decide), m3, u₇.other .r7 (by decide), u₇.other .r2 (by decide), r2₆, r7₆,
      select_min]
    by_cases h : (hdr base s 108).toNat < W
    · simp only [h, decide_true, ↓reduceIte]; omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW]; omega
  · exact ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans ((u₃.rest (by decide)).trans
      (u₄.rest (by decide)))).trans ((R₅.mono (by decide)).trans (R₆.mono (by decide)))).trans
      (((((u₇.rest (by decide)).trans (u₈.rest (by decide))).trans (u₉.rest (by decide))).trans
        (u₁₀.rest (by decide))).trans (m.rest _))
  · rw [m.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, M₆, M₅, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact writeW32_outside _ _ _ (by omega)

theorem digestPrefix_ok {s : State} {base : Addr} {size Q : Nat} (hs : Ws s base size) (hz : 120 ≤ size)
    (h20 : hdr base s 20 = mask32 (Spec.Dsa.bitLength Q = 160))
    (h24 : hdr base s 24 = mask32 (Spec.Dsa.bitLength Q = 224))
    (h28 : hdr base s 28 = mask32 (Spec.Dsa.bitLength Q = 256)) :
    WP isa Shape.digestPrefix s fun t =>
      (hdr base t 112).toNat = min (hdr base s 108).toNat (qWidth Q) ∧
      Rest [.r0, .r2, .r3, .r4, .r5, .r6, .r7] s t ∧ Outside base 112 4 s.mem t.mem := by
  unfold Shape.digestPrefix
  refine VG.Proof.X25519.Arm.WP.append (prefixWidth_ok hs hz h20 h24 h28) fun u ⟨Pu, Ru, Mu⟩ =>
    WP.mono (digestClamp_ok (hs.of_rest Ru (by decide)) hz Pu (by have := qWidth_le Q; omega))
    fun t ⟨Vt, Rt, Ot⟩ => ⟨by rw [Vt, hdr, hdr, Mu], (Ru.mono (by decide)).trans Rt, by rw [← Mu]; exact Ot⟩

/-- The memory the shape's checks change. -/
def shapeRanges : List (Nat × Nat) := [(8, 28), (112, 8), (256, 4704)]

theorem check_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q : Nat} (hs : Ws s base size)
    (hz : 4960 ≤ size) (wp : Width pLen nP) (wq : Width qLen nQ)
    (Rp : Ready s base (.input .p) pLen) (Rq : Ready s base (.input .q) qLen)
    (hP : operand base s (.input .p) pLen = P) (hQ : operand base s (.input .q) qLen = Q) :
    WP isa (Shape.check pLen qLen) s fun t =>
      t.z = decide (¬ shapeValid P Q) ∧ maskW base t = mask32 (shapeValid P Q) ∧
      (hdr base t 112).toNat = min (hdr base s 108).toNat (qWidth Q) ∧
      Rest coreClob s t ∧ Outs base shapeRanges s.mem t.mem := by
  have nw := hs.nowrap
  have fm : Impl.Dsa.Arm.Layout.field .mask = 116 := rfl
  simp only [Shape.check, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (inspectP_ok hs hz wp Rp hP) fun u₁ ⟨E₁, E₂, E₃, E₄, R₁, O₁⟩ => ?_)
  have w₁ := hs.of_rest R₁ (by decide)
  have K₁ : Outs base arithRanges s.mem u₁.mem → True := fun _ => trivial
  have Rq₁ : Ready u₁ base (.input .q) qLen := Rq.keep_rest R₁ (O := O₁) (hO := by decide)
  have Q₁ : operand base u₁ (.input .q) qLen = Q := by
    rw [operand, pointerValue_keep (R₁.gpr .r12 (by decide)) O₁ (by decide) Rq.ok,
      Rq.bytes O₁ (by decide)]
    exact hQ
  refine WP.seq (WP.mono (inspectQ_ok w₁ hz wq Rq₁ Q₁ E₁ E₂ E₃ E₄) fun u₂ ⟨M₂, F₂, F₃, F₄, R₂, O₂⟩ => ?_)
  have w₂ := w₁.of_rest R₂ (by decide)
  refine WP.seq (WP.mono (digestPrefix_ok w₂ (by omega) F₂ F₃ F₄) fun u₃ ⟨D₃, R₃, O₃⟩ => ?_)
  have w₃ := w₂.of_rest R₃ (by decide)
  refine WP.seq (wp_ldr12 w₃ (by decide) (by omega) fun u₄ v₄ => VG.Proof.X25519.Arm.wp_cmp (op2_imm (by decide))
    fun t f z => WP.block_nil (WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩))
  · have m₃ : hdr base u₃ (Impl.Dsa.Arm.Layout.field .mask) = mask32 (shapeValid P Q) := by
      rw [show Impl.Dsa.Arm.Layout.field .mask = 116 from rfl, ← M₂]
      exact hdr_keep (rs := [(112, 4)]) (Outs.of_outside O₃ (by simp)) (by simp) (by omega)
    rw [z, v₄.gpr, m₃]
    by_cases h : shapeValid P Q <;> simp only [mask32, h, ↓reduceIte, decide_true, decide_false, not_true_eq_false,
      not_false_eq_true] <;> decide
  · rw [show maskW base t = maskW base u₃ by simp only [maskW, flagW, f.mem, v₄.mem], ← M₂]
    exact hdr_keep (rs := [(112, 4)]) (Outs.of_outside O₃ (by simp)) (by simp) (by omega)
  · rw [show hdr base t 112 = hdr base u₃ 112 by simp only [hdr, f.mem, v₄.mem], D₃]
    rw [hdr_keep (d := 108) O₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by omega),
      hdr_keep (d := 108) O₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by omega)]
  · exact ((R₁.trans R₂).trans (R₃.mono (by decide))).trans ((v₄.rest (by decide)).trans (f.rest _))
  · rw [f.mem, v₄.mem]
    refine ((Outs.within O₁ ?_).trans (Outs.within O₂ ?_)).trans
      (Outs.within (Outs.of_outside O₃ (List.mem_singleton_self _)) ?_)
    all_goals
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · rcases hr with rfl | rfl | rfl
      · exact ⟨(8, 28), by simp [shapeRanges], by simp only; omega, by simp only; omega⟩
      · exact ⟨(8, 28), by simp [shapeRanges], by simp only; omega, by simp only; omega⟩
      · exact ⟨(256, 4704), by simp [shapeRanges], by simp only; omega, by simp only; omega⟩
    · rcases hr with rfl | rfl | rfl
      · exact ⟨(8, 28), by simp [shapeRanges], by simp only; omega, by simp only; omega⟩
      · exact ⟨(112, 8), by simp [shapeRanges], by simp only; omega, by simp only; omega⟩
      · exact ⟨(256, 4704), by simp [shapeRanges], by simp only; omega, by simp only; omega⟩
    · subst hr
      exact ⟨(112, 8), by simp [shapeRanges], by simp only; omega, by simp only; omega⟩

end VG.Proof.Dsa.Arm
