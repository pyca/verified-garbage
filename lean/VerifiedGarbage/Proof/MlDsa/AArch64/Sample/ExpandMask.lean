import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.ExpandMask

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMaskLoop`. -/
section

/-!
# ML-DSA on AArch64: the loop of `vg_mldsa_expand_mask_poly`

Group `g` of the loop takes the `c/2` bytes `D` of the output from byte `g
c/2` on, and stores the coefficients `4g` to `4g + 3`: coefficient `i` is `γ₁`
minus field `i` of the output, `⌊leNat X / 2^(ic)⌋ mod 2^c`
(`expandMask_getElem`), modulo `q`. The fields are bits of the `u64` of the
group's first 8 bytes (`field_low`), and the last one those above them and the
group's last bytes (`split_div`).
-/

namespace VG.Proof.MlDsa.AArch64.Sample.ExpandMask

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_movk1 wp_addImm wp_subImm wp_strw
  wp_ldrx wp_ldrb wp_sub wp_add wp_lsr wp_lsl wp_and wp_madd wp_x ptr_zero ptr_add toNat_sub_n toNat_add_n
  toNat_lsl_n toNat_byte toNat_lsr toNat_and_mask count_loop)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (lt_bit movQ_ok q_eq)
open VG.Spec.MlDsa (coeffAt Zq q ofInt)

/-- Field `i` of the output `X`. -/
abbrev F (X : List Byte) (c i : Nat) : Nat := leNat X / 2 ^ (i * c) % 2 ^ c

/-- The word of coefficient `i`: `γ₁` minus field `i`, modulo `q`. -/
abbrev Wd (X : List Byte) (c i : Nat) : BitVec 32 :=
  zw (ofInt ((2 ^ (c - 1) : Nat) - (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.F X c i : Nat) : Int))

/-- `γ₁ - v` modulo `q`, from `γ₁` in `x27`, `v` in `x12` and `q` in `x9`,
stored to `[x3 + 4k]`. -/
theorem store_ok {c v : Nat} (hc : c = 18 ∨ c = 20) (hv : v < 2 ^ c) {k : Nat} (hk : k < 4) {s : State}
    {a : Addr} (h12 : (s.gpr .x12).toNat = v) (h27 : (s.gpr .x27).toNat = 2 ^ (c - 1))
    (h9 : (s.gpr .x9).toNat = q) (ha : s.gpr .x3 + BitVec.ofNat 64 (4 * k) = a) (hw : InRegions s.wr a 4) :
    WP isa (.block (emStore k)) s fun s' => Keep [.x13, .x14] s s' ∧
      s'.mem = s.mem.writeW a (zw (ofInt ((2 ^ (c - 1) : Nat) - (v : Nat) : Int))) := by
  refine wp_sub fun s₁ o₁ e₁ => wp_lsr (by decide) fun s₂ o₂ e₂ => wp_madd fun s₃ o₃ e₃ => ?_
  refine wp_strw (a := a) (by constructor <;> omega) (by rw [o₃.get .x3, o₂.get .x3, o₁.get .x3, ha])
    (by rw [o₃.wr, o₂.wr, o₁.wr]; exact hw) fun s₄ o₄ => wp_nil ⟨((o₁.keep.trans o₂.keep).trans
      (o₃.keep.trans o₄.keep)).mono, ?_⟩
  have hq : q = 8380417 := rfl
  have hγ : 2 ^ (c - 1) < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hv' : v < 2 ^ 63 := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega))
  have v14 : (s₂.gpr .x14).toNat = if 2 ^ (c - 1) < v then 1 else 0 := by
    rw [e₂, e₁]; exact lt_bit h27 h12 hγ hv'
  rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, e₃, o₂.get .x13, e₁, o₂.get .x9, o₁.get .x9, zw_toNat, Pack.ofInt_sub (by
    rcases hc with rfl | rfl <;> simp only [Nat.reducePow, hq] at hv ⊢ <;> omega)]
  rw [BitVec.toNat_add, BitVec.toNat_mul, v14, h9, BitVec.toNat_sub, h27, h12]
  have : 2 ^ (c - 1) ≤ 2 ^ 19 := Nat.pow_le_pow_right (by decide) (by omega)
  have : v < 2 ^ 20 := Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [Nat.reducePow, hq] at *
  split <;> omega


theorem hc_even {c : Nat} (hc : c = 18 ∨ c = 20) : c = 2 * (c / 2) := by omega

/-- Field `4g + k` of `X`, from the group `D` of `X` from byte `g c/2`. -/
theorem F_group (X : List Byte) {c : Nat} (hc : c = 18 ∨ c = 20) (g k : Nat) :
    VG.Proof.MlDsa.AArch64.Sample.ExpandMask.F X c (4 * g + k) = leNat (X.drop (g * (c / 2))) / 2 ^ (k * c) % 2 ^ c := by
  rw [VG.Proof.MlDsa.AArch64.Sample.ExpandMask.F, ← leNat_drop, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  rcases hc with rfl | rfl <;> simp only [Nat.reduceDiv] <;> omega

/-- A field of the group's first 8 bytes, `k < 3`, into `x12`. -/
theorem field_low_ok {c : Nat} (hc : c = 18 ∨ c = 20) {k : Nat} (hk : k < 3) {D : List Byte} {s : State}
    (h6 : (s.gpr .x6).toNat = leNat (D.take 8)) (h8 : (s.gpr .x8).toNat = 2 ^ c - 1) :
    WP isa (.block (emField c k)) s fun s' => Only [.x12] s s' ∧
      (s'.gpr .x12).toNat = leNat D / 2 ^ (k * c) % 2 ^ c := by
  unfold emField
  by_cases k0 : k = 0
  · subst k0
    rw [ifT rfl]
    refine wp_and fun s₁ o₁ e₁ => wp_nil ⟨o₁, ?_⟩
    rw [e₁, toNat_and_mask _ _ h8, h6]
    simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
    have := field_low D (P := 0) (c := c) (by omega)
    simpa using this
  · rw [ifF k0, ifT hk]
    have hck : c * k + c ≤ 64 := by rcases hc with rfl | rfl <;> omega
    refine wp_lsr (by omega) fun s₁ o₁ e₁ => wp_and fun s₂ o₂ e₂ => wp_nil ⟨(o₁.trans o₂).mono, ?_⟩
    rw [e₂, toNat_and_mask _ _ (by rw [o₁.get .x8]; exact h8), e₁, toNat_lsr, h6, Nat.mul_comm c k]
    exact field_low D (by rw [Nat.mul_comm k c]; exact hck)

/-- The top field of the group, `k = 3`, into `x12`, from the `u64` of the
first 8 bytes in `x6`, byte 8 in `x7` and, for `c = 20`, byte 9 in `x11`. -/
theorem field_top_ok {c : Nat} (hc : c = 18 ∨ c = 20) {D : List Byte} (hD : c / 2 ≤ D.length) {s : State}
    (h6 : (s.gpr .x6).toNat = leNat (D.take 8)) (h7 : (s.gpr .x7).toNat = (D.getD 8 0).toNat)
    (h11 : c = 20 → (s.gpr .x11).toNat = (D.getD 9 0).toNat) :
    WP isa (.block (emField c 3)) s fun s' => Only [.x12, .x13] s s' ∧
      (s'.gpr .x12).toNat = leNat D / 2 ^ (3 * c) % 2 ^ c := by
  have hA := leNat_lt (D.take 8)
  rw [List.length_take, Nat.min_eq_left (by omega)] at hA
  have b8 := (D.getD 8 0).isLt
  have t9 := leNat_take_succ D (k := 8) (by omega)
  unfold emField
  rw [ifF (by decide), ifF (by decide)]
  rcases hc with rfl | rfl
  · rw [ifF (by decide), List.append_nil]
    refine wp_lsr (by decide) fun s₁ o₁ e₁ => wp_lsl (by decide) fun s₂ o₂ e₂ => wp_add fun s₃ o₃ e₃ =>
      wp_nil ⟨((o₁.trans o₂).trans o₃).mono, ?_⟩
    have v1 : (s₂.gpr .x12).toNat = leNat (D.take 8) / 2 ^ 54 := by rw [o₂.get .x12, e₁, toNat_lsr, h6]
    have v2 : (s₂.gpr .x13).toNat = 2 ^ 10 * (D.getD 8 0).toNat := by
      rw [e₂, toNat_lsl_n (by rw [o₁.get .x7, h7]; simp only [Nat.reducePow] at *; omega), o₁.get .x7, h7,
        Nat.mul_comm]
    have hlt : leNat (D.take 8) / 2 ^ 54 < 2 ^ 10 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; simp only [Nat.reducePow] at *; omega
    rw [e₃, toNat_add_n (by rw [v1, v2]; simp only [Nat.reducePow] at *; omega), v1, v2,
      ← leNat_take_bits D (k := 9) (by omega), t9, show 8 * 8 = 64 from rfl, split_div _ _ (by omega),
      Nat.mod_eq_of_lt (by simp only [Nat.reducePow] at *; omega)]
  · rw [ifT rfl]
    have b9 := (D.getD 9 0).isLt
    have t10 := leNat_take_succ D (k := 9) (by omega)
    refine wp_lsr (by decide) fun s₁ o₁ e₁ => wp_lsl (by decide) fun s₂ o₂ e₂ => wp_add fun s₃ o₃ e₃ =>
      wp_lsl (by decide) fun s₄ o₄ e₄ => wp_add fun s₅ o₅ e₅ =>
      wp_nil ⟨((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).mono, ?_⟩
    have v1 : (s₂.gpr .x12).toNat = leNat (D.take 8) / 2 ^ 60 := by rw [o₂.get .x12, e₁, toNat_lsr, h6]
    have v2 : (s₂.gpr .x13).toNat = 2 ^ 4 * (D.getD 8 0).toNat := by
      rw [e₂, toNat_lsl_n (by rw [o₁.get .x7, h7]; simp only [Nat.reducePow] at *; omega), o₁.get .x7, h7,
        Nat.mul_comm]
    have hlt : leNat (D.take 8) / 2 ^ 60 < 2 ^ 4 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; simp only [Nat.reducePow] at *; omega
    have v3 : (s₃.gpr .x12).toNat = leNat (D.take 8) / 2 ^ 60 + 2 ^ 4 * (D.getD 8 0).toNat := by
      rw [e₃, toNat_add_n (by rw [v1, v2]; simp only [Nat.reducePow] at *; omega), v1, v2]
    have x11 : (s₃.gpr .x11).toNat = (D.getD 9 0).toNat := by
      rw [o₃.get .x11, o₂.get .x11, o₁.get .x11, h11 rfl]
    have v4 : (s₄.gpr .x13).toNat = 2 ^ 12 * (D.getD 9 0).toNat := by
      rw [e₄, toNat_lsl_n (by rw [x11]; simp only [Nat.reducePow] at *; omega), x11, Nat.mul_comm]
    rw [e₅, o₄.get .x12, toNat_add_n (by rw [v3, v4]; simp only [Nat.reducePow] at *; omega), v3, v4,
      ← leNat_take_bits D (k := 10) (by omega), t10, t9, show 8 * 8 = 64 from rfl, show 8 * 9 = 72 from rfl,
      show 2 ^ 72 = 2 ^ 64 * 2 ^ 8 from rfl, Nat.add_assoc (leNat (D.take 8)), Nat.mul_assoc (2 ^ 64),
      ← Nat.mul_add (2 ^ 64), split_div _ _ (by omega),
      Nat.mod_eq_of_lt (by simp only [Nat.reducePow] at *; omega)]
    simp only [Nat.reducePow]
    omega


/-- What the loop needs of the state it starts from: the 640 bytes `X` at
`bP = x25 + 840`, which it may read, `a` at `aP = x26`, which it may write,
and `γ₁ = 2^(c-1)` in `x27`. -/
structure LPre (X : List Byte) (c : Nat) (bP aP : Addr) (s : State) : Prop where
  hc : c = 18 ∨ c = 20
  hX : X.length = 640
  buf : ∀ p < 640, s.mem (bP + BitVec.ofNat 64 p) = X.getD p 0
  inb : ∀ p < 640, InRegions (s.rd ++ s.wr) (bP + BitVec.ofNat 64 p) 1
  inw : ∀ g < 64, InRegions (s.rd ++ s.wr) (bP + BitVec.ofNat 64 (g * (c / 2))) 8
  ina : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4
  disj : (⟨bP, 640⟩ : Region).Disjoint (polyR aP)
  x25 : s.gpr .x25 + BitVec.ofNat 64 840 = bP
  x26 : s.gpr .x26 = aP
  x27 : (s.gpr .x27).toNat = 2 ^ (c - 1)

/-- The registers the loop writes. -/
abbrev lRegs : List Reg := [.x2, .x3, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14]

/-- At the start of group `g`, from the loop's entry state `s₀`. -/
structure EAt (X : List Byte) (c : Nat) (bP aP : Addr) (s₀ : State) (g : Nat) (s : State) : Prop where
  keep : Keep VG.Proof.MlDsa.AArch64.Sample.ExpandMask.lRegs s₀ s
  frame : Frame [polyR aP] s₀.mem s.mem
  x2 : s.gpr .x2 = bP + BitVec.ofNat 64 (g * (c / 2))
  x3 : s.gpr .x3 = aP + BitVec.ofNat 64 (16 * g)
  x5 : (s.gpr .x5).toNat = 64 - g
  x8 : (s.gpr .x8).toNat = 2 ^ c - 1
  x9 : (s.gpr .x9).toNat = q
  st : ∀ i < 4 * g, coeffAt s.mem aP i = VG.Proof.MlDsa.AArch64.Sample.ExpandMask.Wd X c i

/-- After the group's loads and `k` of its coefficients. -/
structure KAt (X : List Byte) (c : Nat) (aP : Addr) (g : Nat) (m₀ : Mem) (s₁ : State) (k : Nat) (u : State) :
    Prop where
  keep : Keep [.x12, .x13, .x14] s₁ u
  frame : Frame [polyR aP] m₀ u.mem
  st : ∀ i < 4 * g + k, coeffAt u.mem aP i = VG.Proof.MlDsa.AArch64.Sample.ExpandMask.Wd X c i

/-- A group: its loads, then its 4 coefficients. -/
theorem body_ok {X : List Byte} {c : Nat} {bP aP : Addr} {s₀ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.ExpandMask.LPre X c bP aP s₀) {g : Nat}
    (hg : g < 64) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.ExpandMask.EAt X c bP aP s₀ g s) :
    WP isa (.block (emBody c)) s fun s' => VG.Proof.MlDsa.AArch64.Sample.ExpandMask.EAt X c bP aP s₀ (g + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ g + 1 ≠ 64) := by
  have hc := hp.hc
  have hcl : (g + 1) * (c / 2) ≤ 640 := by rcases hc with rfl | rfl <;> omega
  have hcl' : g * (c / 2) + c / 2 ≤ 640 := by rw [← Nat.succ_mul]; exact hcl
  have hc2 : c / 2 = 9 ∨ c / 2 = 10 := by omega
  -- the group's bytes
  have mem : ∀ {u : State}, Frame [polyR aP] s₀.mem u.mem → ∀ p < 640,
      u.mem (bP + BitVec.ofNat 64 p) = X.getD p 0 := fun hf p hp' => by
    rw [← hp.buf p hp']
    exact hf _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.disj _ (Offset.contains_base _ (by omega) (by omega))
  have hD : ∀ j, (X.drop (g * (c / 2))).getD j 0 = X.getD (g * (c / 2) + j) 0 := fun j => by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have byte : ∀ j < c / 2, s.mem (s.gpr .x2 + BitVec.ofNat 64 j) = (X.drop (g * (c / 2))).getD j 0 :=
    fun j hj => by rw [h.x2, ptr_add, mem h.frame _ (by omega), hD]
  have hin : ∀ j < c / 2, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [h.keep.rd, h.keep.wr, h.x2, ptr_add]; exact hp.inb _ (by omega)
  have hDl : c / 2 ≤ (X.drop (g * (c / 2))).length := by rw [List.length_drop, hp.hX]; omega
  generalize hDD : X.drop (g * (c / 2)) = D at byte hDl
  have hA : leNat (D.take 8) < 2 ^ 64 := by
    have := leNat_lt (D.take 8); rw [List.length_take, Nat.min_eq_left (by omega)] at this; exact this
  unfold emBody emLoad
  rw [List.append_assoc, WP.block_append_iff, WP.block_append_iff]
  refine wp_ldrx (a := s.gpr .x2) (by decide) (ptr_zero _)
    (by rw [h.keep.rd, h.keep.wr, h.x2]; exact hp.inw g hg) fun s₁ o₁ e₁ => ?_
  refine wp_ldrb (a := s.gpr .x2 + BitVec.ofNat 64 8) (by decide) (by rw [o₁.get .x2])
    (by rw [o₁.rd, o₁.wr]; exact hin 8 (by omega)) fun s₂ o₂ e₂ => ?_
  have v6 : (s₂.gpr .x6).toNat = leNat (D.take 8) := by
    rw [o₂.get .x6, e₁, readW_leNat _ _ D fun k hk => by rw [byte k (by omega)], BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hA]
  have v7 : (s₂.gpr .x7).toNat = (D.getD 8 0).toNat := by rw [e₂, toNat_byte, o₁.mem, byte 8 (by omega)]
  -- the loads, then the coefficients, then the pointers
  have loads : ∀ {Q : State → Prop}, (∀ s₃ : State, Keep [.x6, .x7, .x11] s s₃ → s₃.mem = s.mem →
      (s₃.gpr .x6).toNat = leNat (D.take 8) → (s₃.gpr .x7).toNat = (D.getD 8 0).toNat →
      (c = 20 → (s₃.gpr .x11).toNat = (D.getD 9 0).toNat) → Q s₃) →
      WP isa (.block (if c = 20 then [.ldrb .x11 .x2 9] else [])) s₂ Q := by
    intro Q hQ
    by_cases h20 : c = 20
    · rw [ifT h20]
      refine wp_ldrb (a := s.gpr .x2 + BitVec.ofNat 64 9) (by decide) (by rw [o₂.get .x2, o₁.get .x2])
        (by rw [o₂.rd, o₂.wr, o₁.rd, o₁.wr]; exact hin 9 (by omega)) fun s₃ o₃ e₃ => wp_nil ?_
      exact hQ s₃ ((o₁.keep.trans o₂.keep).trans o₃.keep).mono (by rw [o₃.mem, o₂.mem, o₁.mem])
        (by rw [o₃.get .x6, v6]) (by rw [o₃.get .x7, v7])
        (fun _ => by rw [e₃, toNat_byte, o₂.mem, o₁.mem, byte 9 (by omega)])
    · rw [ifF h20]
      exact wp_nil (hQ s₂ (o₁.keep.trans o₂.keep).mono (by rw [o₂.mem, o₁.mem]) v6 v7 (fun h => absurd h h20))
  refine wp_nil (loads fun s₃ k₃ m₃ x6 x7 x11 => ?_)
  have g8 : (s₃.gpr .x8).toNat = 2 ^ c - 1 := by rw [k₃.get .x8, h.x8]
  have g9 : (s₃.gpr .x9).toNat = q := by rw [k₃.get .x9, h.x9]
  have g27 : (s₃.gpr .x27).toNat = 2 ^ (c - 1) := by rw [k₃.get .x27, h.keep.get .x27, hp.x27]
  have g3 : s₃.gpr .x3 = aP + BitVec.ofNat 64 (16 * g) := by rw [k₃.get .x3, h.x3]
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.KAt X c aP g s.mem s₃) (fun k u hk hu => ?_) 4 (Nat.le_refl _) s₃
    ⟨Keep.refl _ _, by rw [m₃]; exact Frame.refl _ _, fun i hi => by rw [m₃]; exact h.st i (by omega)⟩)
    fun u hu => ?_
  · -- coefficient `4g + k`
    have r : ∀ r ∈ [Reg.x6, .x7, .x11, .x8, .x9, .x27, .x3], u.gpr r = s₃.gpr r := fun r hr =>
      hu.keep.gpr r (by revert hr; revert r; decide)
    have field : WP isa (.block (emField c k)) u fun u' => Only [.x12, .x13] u u' ∧
        (u'.gpr .x12).toNat = leNat D / 2 ^ (k * c) % 2 ^ c := by
      by_cases h3 : k < 3
      · exact WP.mono (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.field_low_ok hc h3 (by rw [r .x6 (by simp), x6]) (by rw [r .x8 (by simp), g8]))
          fun u' ⟨o, v⟩ => ⟨o.mono, v⟩
      · have : k = 3 := by omega
        subst this
        exact WP.mono (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.field_top_ok hc hDl (by rw [r .x6 (by simp), x6]) (by rw [r .x7 (by simp), x7])
          (fun h20 => by rw [r .x11 (by simp), x11 h20])) fun u' ⟨o, v⟩ => ⟨o, by rw [v, Nat.mul_comm]⟩
    rw [WP.block_append_iff]
    refine WP.mono field fun u₁ ⟨k₁, v₁⟩ => ?_
    have ha : u₁.gpr .x3 + BitVec.ofNat 64 (4 * k) = coeffAddr aP (4 * g + k) := by
      rw [k₁.get .x3, r .x3 (by simp), g3, ptr_add, coeffAddr]; congr 2; omega
    refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.store_ok hc (Nat.mod_lt _ (Nat.two_pow_pos c)) (by omega) v₁
      (by rw [k₁.get .x27, r .x27 (by simp), g27]) (by rw [k₁.get .x9, r .x9 (by simp), g9]) ha
      (by rw [k₁.wr, hu.keep.wr, k₃.wr, h.keep.wr]; exact hp.ina _ (by omega))) fun u₂ ⟨k₂, m₂⟩ => ?_
    refine ⟨((hu.keep.trans k₁.keep).trans k₂).mono, ?_, fun i hi => ?_⟩
    · rw [m₂, k₁.mem]
      exact hu.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (by omega))
    · rw [m₂, k₁.mem, coeffAt_writeW _ _ (by omega) (by omega)]
      split
      · rename_i e; subst e
        rw [VG.Proof.MlDsa.AArch64.Sample.ExpandMask.Wd, VG.Proof.MlDsa.AArch64.Sample.ExpandMask.F_group X hc g k, hDD]
      · exact hu.st i (by omega)
  refine wp_addImm (by omega) fun u₁ o₁ e₁ => wp_addImm (by decide) fun u₂ o₂ e₂ => wp_subImm (by decide)
    fun u₃ o₃ e₃ => wp_nil ?_
  have c5 : (u₂.gpr .x5).toNat = 64 - g := by rw [o₂.get .x5, o₁.get .x5, hu.keep.get .x5, k₃.get .x5, h.x5]
  have v5 : (u₃.gpr .x5).toNat = 64 - (g + 1) := by
    rw [e₃, toNat_sub_n (by rw [c5]; simp; omega), c5]; simp; omega
  have m₃ : u₃.mem = u.mem := by rw [o₃.mem, o₂.mem, o₁.mem]
  refine ⟨⟨(((h.keep.trans k₃).trans hu.keep).trans ((o₁.keep.trans o₂.keep).trans o₃.keep)).mono,
    h.frame.trans (by rw [m₃, ← m₃, m₃]; exact hu.frame), ?_, ?_, v5,
    by rw [o₃.get .x8, o₂.get .x8, o₁.get .x8, hu.keep.get .x8, g8],
    by rw [o₃.get .x9, o₂.get .x9, o₁.get .x9, hu.keep.get .x9, g9], fun i hi => by rw [m₃]; exact hu.st i hi⟩,
    by rw [v5]; omega⟩
  · rw [o₃.get .x2, o₂.get .x2, e₁, hu.keep.get .x2, k₃.get .x2, h.x2, ptr_add, Nat.succ_mul]
  · rw [o₃.get .x3, e₂, o₁.get .x3, hu.keep.get .x3, g3, ptr_add]; congr 2


/-- `2ᶜ - 1` into `x8`. -/
theorem mask_ok {c : Nat} (hc : c = 18 ∨ c = 20) {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [.x8] s s' → (s'.gpr .x8).toNat = 2 ^ c - 1 → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x .x8 (BitVec.ofNat 16 (2 ^ (c - 16) - 1)) 1 :: .movk .x .x8 0xffff 0 :: is)) s Q := by
  refine wp_x (d := .x8) rfl fun s₁ o₁ e₁ => wp_x (d := .x8) rfl fun s₂ o₂ e₂ =>
    k s₂ ((o₁.trans o₂).mono fun _ h => by simp only [List.mem_append, List.mem_singleton, or_self] at h; simp [h]) ?_
  rw [e₂]
  simp only [State.read, Size.bits, BitVec.setWidth_eq, e₁]
  rcases hc with rfl | rfl <;> decide

/-- The 64 groups, from the loop's setup: the coefficients of `ExpandMask`. -/
theorem loop_ok {X : List Byte} {c : Nat} {bP aP : Addr} {s₀ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.ExpandMask.LPre X c bP aP s₀) :
    WP isa (emLoop c) s₀ (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.EAt X c bP aP s₀ 64) := by
  unfold emLoop movQ
  refine WP.seq (wp_addImm (by decide) fun s₁ h₁ e₁ => wp_mov fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ =>
    VG.Proof.MlDsa.AArch64.Sample.ExpandMask.mask_ok hp.hc fun s₄ h₄ e₄ => movQ_ok (is := []) fun s₅ h₅ e₅ => wp_nil ?_)
  have k₅ := ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep)
  have m₅ : s₅.mem = s₀.mem := by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have i₀ : VG.Proof.MlDsa.AArch64.Sample.ExpandMask.EAt X c bP aP s₀ 0 s₅ := ⟨k₅.mono, by rw [m₅]; exact Frame.refl _ _,
    by rw [h₅.get .x2, h₄.get .x2, h₃.get .x2, h₂.get .x2, e₁, hp.x25, Nat.zero_mul, ptr_zero],
    by rw [h₅.get .x3, h₄.get .x3, h₃.get .x3, e₂, h₁.get .x26, hp.x26, Nat.mul_zero, ptr_zero],
    by rw [h₅.get .x5, h₄.get .x5, e₃]; rfl, by rw [h₅.get .x8, e₄], e₅, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact count_loop (by decide) (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.EAt X c bP aP s₀) (fun g hg s h => VG.Proof.MlDsa.AArch64.Sample.ExpandMask.body_ok hp hg h) i₀

end VG.Proof.MlDsa.AArch64.Sample.ExpandMask

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_expand_mask_poly`

Correctness: the prologue, the sponge (640 bytes of SHAKE256 of the seed), the
branch on `γ₁` to the loop for `c = 18` or `20` (`ExpandMaskLoop.lean`), and
the epilogue. Constant time: the prologue, and then everything else, by the
taint analysis (the second from registers that correctness makes equal: the
pointers and `γ₁`, which the prologue zero-extends from `w1`).
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep only_write wp_nil wp_lsr toNat_lsr eval_zero eq_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H PolyIs coeffAt toRq bitUnpack bitlen)
open VG.Spec.Sha3 (bytesAt)

/-- `γ₁`, the `u32` argument in `w1`. -/
abbrev gammaOf (s : State) : Nat := ((s.gpr .x1).setWidth 32).toNat

/-- `vg_mldsa_expand_mask_poly(seed = x0, gamma1 = w1, a = x2, scratch = x3)`,
with 16 bytes of stack below `sp`. -/
def emK : Contract isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 66⟩
    let a : Region := ⟨s.gpr .x2, 1024⟩
    let scratch : Region := ⟨s.gpr .x3, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [a, scratch] ∧ seed.Disjoint a ∧ seed.Disjoint scratch ∧
    a.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint a ∧
    stack.Disjoint scratch ∧ (VG.Proof.MlDsa.AArch64.Sample.gammaOf s = 2 ^ 17 ∨ VG.Proof.MlDsa.AArch64.Sample.gammaOf s = 2 ^ 19)
  post s s' :=
    PolyIs s'.mem (s.gpr .x2) (toRq (bitUnpack (H (bytesAt s.mem (s.gpr .x0) 66)
      (32 * (1 + bitlen (VG.Proof.MlDsa.AArch64.Sample.gammaOf s - 1)))) (VG.Proof.MlDsa.AArch64.Sample.gammaOf s - 1) (VG.Proof.MlDsa.AArch64.Sample.gammaOf s)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ (s₁.gpr .x1).setWidth 32 = (s₂.gpr .x1).setWidth 32 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

namespace ExpandMask

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .x0, 66, σ.gpr .x3, σ.gpr .x2, ((σ.gpr .x1).setWidth 32).setWidth 64⟩

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H ((VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ).msg σ) 640

section
variable {σ : State} (hp : emK.pre σ)
include hp

theorem spOk : SpOk (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1, by show (66 : Nat) < 2 ^ 64; decide⟩

theorem gamma : VG.Proof.MlDsa.AArch64.Sample.gammaOf σ = 2 ^ 17 ∨ VG.Proof.MlDsa.AArch64.Sample.gammaOf σ = 2 ^ 19 := hp.2.2.2.2.2.2.2.2.2

theorem pro_ok : WP isa (.block (pro .x3 .x2 (.addImm .w .x27 .x1 0) (.movz .x .x4 66 0))) σ (J0 (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ) σ) :=
  Sample.pro_ok (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOk hp) rfl rfl (by decide) rfl
    (fun s hs => ⟨_, rfl, only_write _ _ _ _, by
      simp only [State.write, State.read, ite_true, hs .x1 (by decide) (by decide)]
      congr 1
      exact BitVec.add_zero _⟩)
    (fun s _ => ⟨_, rfl, only_write _ _ _ _, by rfl⟩)

omit hp in
theorem x27_toNat {s : State} (h : Env (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ) σ s) : (s.gpr .x27).toNat = VG.Proof.MlDsa.AArch64.Sample.gammaOf σ := by
  rw [h.x27]; simp; omega

/-- The loop for `c`. -/
theorem loop_ok' {s : State} (h : J6 136 640 (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ) σ s) {c : Nat} (hc : c = emC (VG.Proof.MlDsa.AArch64.Sample.gammaOf σ)) :
    WP isa (emLoop c) s fun s' => Env (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ) σ s' ∧
      ∀ i < 256, coeffAt s'.mem (σ.gpr .x2) i = ExpandMask.Wd (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.X σ) c i := by
  have hg := VG.Proof.MlDsa.AArch64.Sample.ExpandMask.gamma hp
  obtain ⟨_, _, e3⟩ := emC_eq hg
  have hc' : c = 18 ∨ c = 20 := by subst hc; unfold emC; split <;> simp
  have lp : ExpandMask.LPre (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.X σ) c ((VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ).at' 840) (σ.gpr .x2) s :=
    ⟨hc', VG.Proof.MlDsa.Sample.H_length _ _, fun p hp' => by rw [VG.Proof.MlDsa.AArch64.Sample.ExpandMask.X, VG.Proof.MlDsa.Sample.H_eq, ← h.out, MlKem.bytesAt_getD _ _ hp'],
      fun p hp' => by rw [at_add]; exact inScrRd (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOk hp) h.env.rd h.env.wr (by omega),
      fun g hg' => by
        rw [at_add]; exact inScrRd (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOk hp) h.env.rd h.env.wr (by rcases hc' with rfl | rfl <;> omega),
      fun i hi => inA (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOk hp) h.env.wr hi, (a_scr' (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOk hp) (by omega)).symm, by rw [h.env.x25],
      h.env.x26, by rw [VG.Proof.MlDsa.AArch64.Sample.ExpandMask.x27_toNat h.env, e3, hc]⟩
  exact WP.mono (ExpandMask.loop_ok lp) fun u hu => ⟨h.env.keepA (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOk hp) hu.keep hu.frame, hu.st⟩

end

theorem correctWith (v : Proof.Sha3.AArch64.Permutation) (σ : State) (hp : emK.pre σ) :
    ∃ t s', Exec isa (expandMaskWith v.callee) σ t s' ∧ abiPreserved σ s' ∧ emK.post σ s' := by
  have hg := VG.Proof.MlDsa.AArch64.Sample.ExpandMask.gamma hp
  obtain ⟨e1, e2, e3⟩ := emC_eq hg
  refine WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (spongeWith_ok (v := v) (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOk hp) (rate := 136) (outlen := 640) (by decide) (by decide) h1)
      fun s h2 => ?_))
  refine WP.seq (WP.mono (Q := fun (u : State) => Env (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ) σ u ∧
    ∀ i < 256, coeffAt u.mem (σ.gpr .x2) i = ExpandMask.Wd (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.X σ) (emC (VG.Proof.MlDsa.AArch64.Sample.gammaOf σ)) i) ?_
    fun u ⟨he, hst⟩ => WP.mono (epi_ok (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOk hp) he) fun s' ⟨abi, m, _⟩ => ⟨abi, by
      show PolyIs s'.mem _ _
      rw [m]
      refine polyIs_of_coeffAt fun i hi => ?_
      rw [hst i hi, expandMask_getElem _ hg hi, ExpandMask.Wd, ExpandMask.F, ← e3]⟩)
  refine WP.seq (wp_lsr (by decide) fun s₁ o₁ e₁ => wp_nil ?_)
  -- the branch on `γ₁`
  have x9 : (s₁.gpr .x9).toNat = VG.Proof.MlDsa.AArch64.Sample.gammaOf σ / 2 ^ 18 := by
    rw [e₁, toNat_lsr, VG.Proof.MlDsa.AArch64.Sample.ExpandMask.x27_toNat h2.env]
  have h6 : J6 136 640 (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ) σ s₁ := ⟨h2.env.keep o₁.keep o₁.mem, by rw [o₁.mem]; exact h2.out⟩
  rcases hg with hg | hg
  · have ec : emC (VG.Proof.MlDsa.AArch64.Sample.gammaOf σ) = 18 := by unfold emC; rw [hg]; rfl
    refine WP.ite true (by rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, x9, hg]; rfl) (fun _ => ?_) (fun h => nomatch h)
    rw [ec]; exact VG.Proof.MlDsa.AArch64.Sample.ExpandMask.loop_ok' hp h6 ec.symm
  · have ec : emC (VG.Proof.MlDsa.AArch64.Sample.gammaOf σ) = 20 := by unfold emC; rw [hg]; rfl
    refine WP.ite false (by rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, x9, hg]; rfl) (fun h => nomatch h) (fun _ => ?_)
    rw [ec]; exact VG.Proof.MlDsa.AArch64.Sample.ExpandMask.loop_ok' hp h6 ec.symm

theorem correct (σ : State) (hp : emK.pre σ) :
    ∃ t s', Exec isa expandMask σ t s' ∧ abiPreserved σ s' ∧ emK.post σ s' :=
  VG.Proof.MlDsa.AArch64.Sample.ExpandMask.correctWith .scalar σ hp

/-! ## Constant time -/

theorem pub_eq {σ₁ σ₂ : State} (hq : emK.pub σ₁ σ₂) : VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ₁ = VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ₂ := by
  rw [VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf, VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]

theorem ctWith (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa emK.pre emK.pub (expandMaskWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.mldsaMaskTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True)
    (P := Rel2 emK.pre emK.pub fun σ s => s = σ)
    ?_ (fun s₁ s₂ h => ⟨s₁, s₂, h.1, h.2.1, h.2.2, rfl, rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (VG.Proof.MlDsa.AArch64.Sample.ExpandMask.spOf σ) σ) [.x0, .x2, .x3]
    (fun σ s hp h => by subst h; exact VG.Proof.MlDsa.AArch64.Sample.ExpandMask.pro_ok hp) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂
      exact ⟨hq.2.2.2.2, RejNtt.regs3 hq.1 hq.2.2.1 hq.2.2.2.1⟩) (by taint_decide)) ?_
  exact vectorRelTaint [.x25, .x26, .x27, .x3, .x4] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, VG.Proof.MlDsa.AArch64.Sample.ExpandMask.pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, VG.Proof.MlDsa.AArch64.Sample.ExpandMask.pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, VG.Proof.MlDsa.AArch64.Sample.ExpandMask.pub_eq hq]
      · rw [h₁.x3, h₂.x3, VG.Proof.MlDsa.AArch64.Sample.ExpandMask.pub_eq hq]
      · exact toNat_inj h₁.x4 h₂.x4) hhint

theorem ct : ConstantTime isa emK.pre emK.pub expandMask :=
  VG.Proof.MlDsa.AArch64.Sample.ExpandMask.ctWith .scalar

end ExpandMask

/-- A state satisfying the precondition. -/
def emSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x20000 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem expandMask_verifiedWith (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target (Impl.MlDsa.AArch64.Sample.expandMaskWith v.callee)
    (Spec.MlDsa.expandMaskContract AArch64.abi 16) :=
  Verified.of_correct (ExpandMask.correctWith v) (ExpandMask.ctWith v)
    { pre := by sig_implies_pre [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, VG.Proof.MlDsa.AArch64.Sample.emK,
        AArch64.abi, AArch64.argRegs]
      post := by sig_implies_post [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, VG.Proof.MlDsa.AArch64.Sample.emK,
        AArch64.abi, AArch64.argRegs]
      pub := by sig_implies_pub [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, VG.Proof.MlDsa.AArch64.Sample.emK,
        AArch64.abi, AArch64.argRegs]
      sat := by sig_implies_sat [Spec.MlDsa.expandMaskContract, Spec.MlDsa.expandMaskSig, VG.Proof.MlDsa.AArch64.Sample.emK,
        AArch64.abi, AArch64.argRegs] [emSat] using VG.Proof.MlDsa.AArch64.Sample.emSat }

theorem expandMask_verified : Verified AArch64.target Impl.MlDsa.AArch64.Sample.expandMask
    (Spec.MlDsa.expandMaskContract AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.Sample.expandMask_verifiedWith .scalar

end VG.Proof.MlDsa.AArch64.Sample

end
