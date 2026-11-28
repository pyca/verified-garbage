module

-- separate module: `XK` past a block's changes and a lane's chain, which the steps' proofs do not change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyXmssBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `xmssPk`: the lanes of a group of chains

The branch-free arithmetic of the code (`lt_bit`, `clamp_eq`, `min_eq`): a
lane's chain `c = min(c₀ + k, len - 1)` and its digit (`chainOf_ok`), and the
group's first step, the least of its digits.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.XmssPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.MlKem.AArch64 (Only Keep)
variable {p : Params}

open VG.Proof.SlhDsa.AArch64.TreeBase (Up in_scr in_scr' wp_addi wp_subi wp_subr wp_lsr wp_movz wp_and wp_eor
  wp_addr wp_ldrb)

/-! ## Arithmetic -/

theorem lt_bit {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega_using [ha]), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_using [hb])]
  split
  · rename_i h
    rw [BitVec.toNat_ofNat]
    have e : (2 ^ 64 - b + a) % 2 ^ 64 = 2 ^ 64 - (b - a) := by
      rw [Nat.mod_eq_of_lt (by omega_using [h, ha, hb])]; omega_using [h, ha, hb]
    rw [e]
    show _ = 1
    omega_using [h, ha, hb]
  · rename_i h
    rw [BitVec.toNat_ofNat]
    have e : (2 ^ 64 - b + a) % 2 ^ 64 = a - b := by
      rw [show 2 ^ 64 - b + a = (a - b) + 2 ^ 64 by omega_using [h, hb], Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega_using [ha])]
    rw [e]
    show _ = 0
    omega_using [h, ha]

theorem neg_bit (q : Prop) [Decidable q] :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if q then 1 else 0)) = if q then BitVec.allOnes 64 else 0 := by
  by_cases h : q <;> simp [h] <;> decide

/-- The chain of a lane: `c₀ - ((c₀ - L) & mask)`, `mask` all ones iff `c₀ > L`. -/
theorem clamp_eq {c₀ L : Nat} (hc : c₀ < 2 ^ 62) (hL : L < 2 ^ 62) :
    BitVec.ofNat 64 c₀ - ((BitVec.ofNat 64 c₀ - BitVec.ofNat 64 L) &&&
      (BitVec.ofNat 64 0 - (BitVec.ofNat 64 L - BitVec.ofNat 64 c₀) >>> 63)) = BitVec.ofNat 64 (min c₀ L) := by
  rw [lt_bit (by omega_using [hL]) (by omega_using [hc]), neg_bit]
  by_cases h : L < c₀
  · simp only [h, ↓reduceIte, BitVec.and_allOnes]
    rw [Nat.min_eq_right (by omega_using [h])]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [h, hc, hL]
  · simp [h]
    rw [Nat.min_eq_left (by omega_using [h])]

/-- The least of two digits: `d ^ ((d ^ m) & mask)`, `mask` all ones iff `m < d`. -/
theorem min_eq {m d : Nat} (hm : m < 2 ^ 62) (hd : d < 2 ^ 62) :
    ((BitVec.ofNat 64 d ^^^ BitVec.ofNat 64 m) &&&
      (BitVec.ofNat 64 0 - (BitVec.ofNat 64 m - BitVec.ofNat 64 d) >>> 63)) ^^^ BitVec.ofNat 64 d =
      BitVec.ofNat 64 (min m d) := by
  rw [lt_bit (by omega_using [hm]) (by omega_using [hd]), neg_bit]
  by_cases h : m < d
  · simp only [h, ↓reduceIte, BitVec.and_allOnes]
    rw [Nat.min_eq_left (by omega_using [h]), BitVec.xor_assoc, BitVec.xor_comm (BitVec.ofNat 64 m),
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [h]
    rw [Nat.min_eq_right (by omega_using [h])]

theorem upOnly {s s' : State} {d : Reg} {x : BitVec 64} (h : Up s s' d x) : Only [d] s s' :=
  ⟨fun r hr => h.other r (by simpa using hr), h.mem, h.rd, h.wr, h.sp, fun r _ => by rw [h.v]⟩

/-! ## A lane's chain and digit -/

/-- The chain of lane `k` of group `g`. -/
def cOf (p : Params) (g k : Nat) : Nat := min (4 * g + k) (p.len - 1)

theorem imm16 {v : Nat} (h : v < 65536) : (BitVec.ofNat 16 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [h]

theorem digit_byte (m : Mem) (S : Addr) (i : Nat) :
    (m (at' S (Layout.oDigits + i))).setWidth 64 = BitVec.ofNat 64 (digitAt m S i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [digitAt, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- `chainOf p k`: the chain of lane `k` of group `g` (`x22 = 4g`) to `x10`,
its digit to `x11`. -/
theorem chainOf_ok (hz : Sz p) {g k : Nat} (hg : 4 * g < p.len) (hk : k < 4) {t : State} {S : Addr}
    (h19 : t.gpr .x19 = S) (h22 : t.gpr .x22 = BitVec.ofNat 64 (4 * g)) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    {is : List Instr} {Q : State → Prop}
    (K : ∀ t', Only [.x10, .x13, .x14, .x15, .x11] t t' → t'.gpr .x10 = BitVec.ofNat 64 (cOf p g k) →
      t'.gpr .x11 = BitVec.ofNat 64 (digitAt t.mem S (cOf p g k)) → WP isa (.block is) t' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.chainOf p k ++ is)) t Q := by
  have hl := hz.len
  have hn32 := hz.n32
  have hL : p.len - 1 < 65536 := by omega_using [hl, hn32]
  simp only [Impl.SlhDsa.AArch64.Verify.chainOf, List.cons_append, List.nil_append]
  refine wp_addi (by omega_using [hk]) fun t₁ u₁ => wp_movz fun t₂ u₂ => wp_subr fun t₃ u₃ =>
    wp_lsr (by decide) fun t₄ u₄ => wp_subi (by omega_using [hl, hn32]) fun t₅ u₅ => wp_movz fun t₆ u₆ =>
    wp_subr fun t₇ u₇ => wp_and fun t₈ u₈ => wp_subr fun t₉ u₉ => wp_addr fun t₁₀ u₁₀ => ?_
  have hc₀ : 4 * g + k < 2 ^ 62 := by omega_using [hg, hk, hl, hn32]
  have v₁ : t₁.gpr .x10 = BitVec.ofNat 64 (4 * g + k) := by rw [u₁.gpr, h22, BitVec.ofNat_add]
  have v₃ : t₃.gpr .x13 = BitVec.ofNat 64 (p.len - 1) - BitVec.ofNat 64 (4 * g + k) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), v₁, imm16 hL]
  have v₄ : t₄.gpr .x13 = (BitVec.ofNat 64 (p.len - 1) - BitVec.ofNat 64 (4 * g + k)) >>> 63 := by
    rw [u₄.gpr, v₃]
  have x10₄ : t₄.gpr .x10 = BitVec.ofNat 64 (4 * g + k) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), v₁]
  have v₅ : t₅.gpr .x14 = BitVec.ofNat 64 (4 * g + k) - BitVec.ofNat 64 (p.len - 1) := by rw [u₅.gpr, x10₄]
  have v₇ : t₇.gpr .x15 = BitVec.ofNat 64 0 - (BitVec.ofNat 64 (p.len - 1) - BitVec.ofNat 64 (4 * g + k)) >>> 63 := by
    rw [u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide), v₄]; rfl
  have v₈ : t₈.gpr .x14 = (BitVec.ofNat 64 (4 * g + k) - BitVec.ofNat 64 (p.len - 1)) &&&
      (BitVec.ofNat 64 0 - (BitVec.ofNat 64 (p.len - 1) - BitVec.ofNat 64 (4 * g + k)) >>> 63) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), v₅, v₇]
  have v₉ : t₉.gpr .x10 = BitVec.ofNat 64 (cOf p g k) := by
    rw [u₉.gpr, v₈, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      x10₄, clamp_eq hc₀ (by omega_using [hl, hn32])]
    rfl
  have g19 : t₉.gpr .x19 = S := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h19]
  have hcl : cOf p g k < p.len := by simp only [cOf]; omega_using [hl, hn32]
  have m₁₀ : t₁₀.mem = t.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine wp_ldrb (a := at' S (Layout.oDigits + cOf p g k)) (by decide)
    (by rw [u₁₀.gpr, g19, v₉, addr_add, Nat.add_comm])
    (by rw [u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr,
      u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact in_scr' hw (by simp only [Layout.oDigits]; omega_using [hcl, hl, hn32]))
    fun t₁₁ u₁₁ => K t₁₁ ?_ ?_ ?_
  · exact (((((((((((upOnly u₁).trans (upOnly u₂)).trans (upOnly u₃)).trans (upOnly u₄)).trans (upOnly u₅)).trans (upOnly u₆)).trans
      (upOnly u₇)).trans (upOnly u₈)).trans (upOnly u₉)).trans (upOnly u₁₀)).trans (upOnly u₁₁)).mono (by simp)
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), v₉]
  · rw [u₁₁.gpr, m₁₀, digit_byte]

/-! ## What `xmssPk` may write -/

/-- An offset range of `scratch` the code may write: `thash4`'s work, the
message at `oMsg`, or a lane's tail (from `n + 16`, past its `PK.seed` and
`a16`). -/
def Safe (p : Params) (o l : Nat) : Prop :=
  o + l ≤ workUsed ∨ (Layout.oMsg ≤ o ∧ o + l ≤ Layout.oMsg + 64) ∨
    ∃ k < 4, (Layout.laneA k + p.n + 16 ≤ o ∧ o + l ≤ Layout.laneA k + Layout.strideA) ∨
      (Layout.laneB k + p.n + 16 ≤ o ∧ o + l ≤ Layout.laneB k + Layout.strideB)

theorem Safe.sub (hz : Sz p) {o l : Nat} (h : Safe p o l) (S : Addr) :
    ∃ R ∈ changes p S, Region.Sub ⟨at' S o, l⟩ R := by
  have hn32 := hz.n32
  rcases h with h | ⟨h₁, h₂⟩ | ⟨k, hk, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
  · exact ⟨⟨S, workUsed⟩, by simp [changes], Offset.sub_base S h⟩
  · exact ⟨⟨at' S Layout.oMsg, 64⟩, by simp [changes], Offset.sub S h₁ h₂⟩
  · refine ⟨⟨at' S (Layout.laneA k + p.n + 16), Layout.strideA - p.n - 16⟩, ?_, Offset.sub S h₁ (by
      simp only [Layout.strideA] at h₂ ⊢; omega_using [h₂, hn32])⟩
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_cons_self⟩))
  · refine ⟨⟨at' S (Layout.laneB k + p.n + 16), Layout.strideB - p.n - 16⟩, ?_, Offset.sub S h₁ (by
      simp only [Layout.strideB] at h₂ ⊢; omega_using [h₂, hn32])⟩
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_cons_of_mem _ List.mem_cons_self⟩))

/-- A safe range is apart from the saved slots, the digits and the lanes'
`PK.seed` and `a16`. -/
theorem Safe.apart (hz : Sz p) {o l : Nat} (h : Safe p o l) {o' l' : Nat}
    (h' : (1152 ≤ o' ∧ o' + l' ≤ 1224) ∨ (Layout.oDigits ≤ o' ∧ o' + l' ≤ Layout.oDigits + 128) ∨
      ∃ k < 4, (Layout.laneA k ≤ o' ∧ o' + l' ≤ Layout.laneA k + p.n + 16) ∨
        (Layout.laneB k ≤ o' ∧ o' + l' ≤ Layout.laneB k + p.n + 16)) :
    o + l ≤ o' ∨ o' + l' ≤ o := by
  have hn32 := hz.n32
  have hn16 := hz.n16
  simp only [Safe, workUsed, Layout.oMsg, Layout.oDigits, Layout.laneA, Layout.laneB, Layout.oA, Layout.oB,
    Layout.strideA, Layout.strideB] at h h' ⊢
  rcases h with h | ⟨h₁, h₂⟩ | ⟨k, hk, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ <;>
  rcases h' with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ | ⟨k', hk', ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩⟩ <;>
  first
    | omega
    | (rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> omega)
    | (rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> omega)
    | (rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
        rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> omega)

theorem Safe.lt (hz : Sz p) {o l : Nat} (h : Safe p o l) : o + l ≤ 65536 := by
  have hn32 := hz.n32
  simp only [Safe, workUsed, Layout.oMsg, Layout.laneA, Layout.laneB, Layout.oA, Layout.oB, Layout.strideA,
    Layout.strideB] at h
  omega

/-- A range apart from every safe one, as `Region.Disjoint`. -/
theorem safe_disj (hz : Sz p) {S : Addr} {W : List Region} (hW : ∀ r ∈ W, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l)
    {o' l' : Nat} (h' : (1152 ≤ o' ∧ o' + l' ≤ 1224) ∨ (Layout.oDigits ≤ o' ∧ o' + l' ≤ Layout.oDigits + 128) ∨
      ∃ k < 4, (Layout.laneA k ≤ o' ∧ o' + l' ≤ Layout.laneA k + p.n + 16) ∨
        (Layout.laneB k ≤ o' ∧ o' + l' ≤ Layout.laneB k + p.n + 16)) :
    ∀ r ∈ W, Region.Disjoint ⟨at' S o', l'⟩ r := by
  have hn32 := hz.n32
  have hb : o' + l' ≤ 65536 := by
    simp only [Layout.oDigits, Layout.laneA, Layout.laneB, Layout.oA, Layout.oB, Layout.strideA, Layout.strideB] at h'
    omega
  intro r hr
  obtain ⟨o, l, rfl, hs⟩ := hW r hr
  have := (Safe.apart hz hs h').symm
  exact Offset.disjoint S this (by omega) (by have := Safe.lt hz hs; omega)

/-- `XK` past a block that writes the registers `R` and safe ranges `W` only. -/
theorem XK.step (hz : Sz p) {σ t t' : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hx : XK p σ S sig pk a D t) {R : List Reg} (hR : ∀ r ∈ [Reg.x19, .x20, .x21, .x27, .x28], r ∉ R)
    (hk : Keep R t t') {W : List Region} (hf : Frame W t.mem t'.mem)
    (hW : ∀ r ∈ W, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l) : XK p σ S sig pk a D t' := by
  have hn32 := hz.n32
  have hl := hz.len
  have keepB : ∀ {o' l' : Nat}, _ → bytesAt t'.mem (at' S o') l' = bytesAt t.mem (at' S o') l' :=
    fun {o' l'} h' => TreeBase.bytesAt_frame hf (safe_disj hz hW (o' := o') (l' := l') h') (by
      simp only [Layout.oDigits, Layout.laneA, Layout.laneB, Layout.oA, Layout.oB] at h'; omega)
  refine ⟨by rw [hk.gpr _ (hR _ (by simp)), hx.x19], by rw [hk.gpr _ (hR _ (by simp)), hx.x20],
    by rw [hk.gpr _ (hR _ (by simp)), hx.x21], fun r hr => by rw [hk.gpr _ (hR r (by simp at hr; rcases hr with rfl | rfl <;> simp)), hx.kept r hr],
    by rw [hk.sp, hx.sp], by rw [hk.rd, hx.rd], by rw [hk.wr, hx.wr], fun r hr => by rw [hk.vcs r hr, hx.vcs r hr],
    ⟨fun k hk' => ?_, fun k hk' => ?_, fun k hk' => ?_, fun k hk' => ?_⟩,
    saved_keep hx.saved hf (safe_disj hz hW (.inl ⟨Nat.le_refl _, Nat.le_refl _⟩)), fun i hi => ?_,
    hx.frame.trans (hf.sub fun r hr => by obtain ⟨o, l, rfl, hs⟩ := hW r hr; exact Safe.sub hz hs S)⟩
  · rw [keepB (o' := Layout.laneA k) (l' := p.n) (.inr (.inr ⟨k, hk', .inl ⟨Nat.le_refl _, by omega⟩⟩)), hx.env.seedA k hk']
  · rw [keepB (o' := Layout.laneB k) (l' := p.n) (.inr (.inr ⟨k, hk', .inr ⟨Nat.le_refl _, by omega⟩⟩)), hx.env.seedB k hk']
  · rw [keepB (o' := Layout.laneA k + p.n) (l' := 16) (.inr (.inr ⟨k, hk', .inl ⟨by omega, by omega⟩⟩)),
      hx.env.adrsA k hk']
  · rw [keepB (o' := Layout.laneB k + p.n) (l' := 16) (.inr (.inr ⟨k, hk', .inr ⟨by omega, by omega⟩⟩)),
      hx.env.adrsB k hk']
  · have e := keepB (o' := Layout.oDigits + i) (l' := 1) (.inr (.inl ⟨by omega, by omega⟩))
    simp only [digitAt]
    have e' := congrArg (fun l => l.getD 0 0) e
    simp only [bytesAt_getD _ _ (show 0 < 1 by decide), BitVec.add_zero] at e'
    rw [e']; exact hx.dig i hi

end VG.Proof.SlhDsa.AArch64.XmssPk
