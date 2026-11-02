module

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillDep
public import VerifiedGarbage.Proof.Argon2.AddressInput
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Initial
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillSteps
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on RISC-V: the address-generation input block

`input_ok`: `clearAt s4 1024`, `clearAt s0 1024` and `addressHeader` leave
the input block of §3.4.1.2 (`Proof.Argon2.addressInput`) at
`scratch + 1024` and a zero block at `scratch + 3072`, writing only those two
blocks.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)
open VG.RISCV64.Wp (Upd Mupd wp_li)
open VG.Spec.Argon2 (Block zeroBlock)
open VG.Impl.Argon2.RISCV64.Derive (passOff laneOff sliceOff counterOff ld lda ldw)

/-- Doublewords of `scratch`. -/
abbrev sd (s₀ : State) (m : Mem) (o : Nat) : BitVec 64 := m.readW (scrP s₀ + BitVec.ofNat 64 o) 64

/-- A doubleword of `scratch` after a store to another, or the same. -/
theorem sd_store {s₀ : State} (m : Mem) {a b : Nat} (ha : a + 8 ≤ 16384) (hb : b + 8 ≤ 16384)
    (h : a = b ∨ a + 8 ≤ b ∨ b + 8 ≤ a) (v : BitVec 64) :
    sd s₀ (m.writeW (scrP s₀ + BitVec.ofNat 64 a) v) b = if a = b then v else sd s₀ m b := by
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self64 _ _ _
  · rw [ite_eq_right e]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

/-- A block of `scratch`, from its doublewords. -/
theorem blockAt_of_sd {s₀ : State} {m : Mem} {o : Nat} {f : Nat → BitVec 64}
    (h : ∀ i < 128, sd s₀ m (o + 8 * i) = f i) :
    blockAt m (scrP s₀ + BitVec.ofNat 64 o) = Vector.ofFn fun j : Fin 128 => f j.val := by
  apply Vector.ext
  intro j hj
  rw [blockAt_get _ _ hj, Vector.getElem_ofFn, ← h j hj, sd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `n` stores of `a0 = 0` to `b + d + 8k`, with `b` pointing `B` bytes into
`scratch`. -/
theorem zeros_ok {s : State} (h : Inv s₀ s) {b : Reg} {B : Nat}
    (hb : s.gpr b = scrP s₀ + BitVec.ofNat 64 B) {d : Nat} (hd : B + d + 1024 ≤ 4096)
    (hd' : d + 1024 ≤ 2048) (hd8 : (B + d) % 8 = 0) (ha : s.gpr .a0 = 0) :
    ∀ n ≤ 128, WP isa (.block ((List.range n).map fun k => Instr.store .d .a0 b (d + 8 * k))) s
      fun t => Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨scrP s₀ + BitVec.ofNat 64 (B + d), 1024⟩] s.mem t.mem ∧
        ∀ i < n, sd s₀ t.mem (B + d + 8 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((zeros_ok h hb hd hd' hd8 ha n (by omega_arith)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have hc' : (⟨scrP s₀ + BitVec.ofNat 64 (B + d), 1024⟩ : Region).Contains
        (scrP s₀ + BitVec.ofNat 64 (B + (d + 8 * n))) 8 :=
      Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
    refine wp_stscrb hp it (b := b) (B := B) (by rw [gt, hb]) (o := d + 8 * n) (by omega_arith)
      (by omega_arith) (by omega_arith) fun t₁ i₁ m₁ g₁ _ _ => WP.block_nil ⟨i₁, by rw [g₁, gt], ?_, fun i hi => ?_⟩
    · rw [m₁]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [m₁, gt, ha, sd_store _ (by omega_arith) (by omega_arith) (by omega_arith)]
      by_cases e : B + (d + 8 * n) = B + d + 8 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact wt i (by omega_arith)

/-- `clearAt b d`: zero `scratch[B + d, B + d + 1024)`. -/
theorem clearAt_ok {s : State} (h : Inv s₀ s) {b : Reg} (hba : b ≠ .a0) {B : Nat}
    (hb : s.gpr b = scrP s₀ + BitVec.ofNat 64 B) {d : Nat} (hd : B + d + 1024 ≤ 4096)
    (hd' : d + 1024 ≤ 2048) (hd8 : (B + d) % 8 = 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ r, r ≠ .a0 → t.gpr r = s.gpr r) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 (B + d), 1024⟩] s.mem t.mem →
      (∀ i < 128, sd s₀ t.mem (B + d + 8 * i) = 0) → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.clearAt b d ++ is)) s Q := by
  unfold Impl.Argon2.RISCV64.Derive.clearAt
  simp only [List.cons_append]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁
  refine WP.block_append ((zeros_ok hp i₁ (by rw [u₁.other _ hba, hb]) hd hd' hd8 u₁.gpr 128
    (Nat.le_refl _)).mono fun t ⟨it, gt, ft, wt⟩ => k t it (fun r a => ?_) ?_ wt)
  · rw [gt, u₁.other _ a]
  · rw [show s.mem = s₁.mem by rw [u₁.mem]]; exact ft

end

/-- The seven doublewords of the address-generation input block. -/
def hdr (s₀ : State) (pass lane slice c : Nat) : Nat → BitVec 64
  | 0 => BitVec.ofNat 64 pass
  | 1 => BitVec.ofNat 64 lane
  | 2 => BitVec.ofNat 64 slice
  | 3 => arg s₀ 14
  | 4 => (arg32 s₀ 5).setWidth 64
  | 5 => (arg32 s₀ 0).setWidth 64
  | _ => BitVec.ofNat 64 c

/-- The doublewords of the input block after its first `n` are written over `m`'s. -/
def HW (s₀ : State) (m : Mem) (pass lane slice c n : Nat) (m' : Mem) : Prop :=
  ∀ i < 128, sd s₀ m' (1024 + 8 * i) = if i < n then hdr s₀ pass lane slice c i else sd s₀ m (1024 + 8 * i)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One doubleword of the header. -/
theorem hdr_step {m : Mem} {pass lane slice c n : Nat} (hn : n < 7) {u : State} (h : Inv s₀ u)
    (ha : u.gpr .a0 = hdr s₀ pass lane slice c n) (hw : HW s₀ m pass lane slice c n u.mem)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.gpr = u.gpr → Frame [⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩] u.mem t.mem →
      HW s₀ m pass lane slice c (n + 1) t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store .d .a0 .s4 (1024 + 8 * n) :: is)) u Q := by
  have hc' : (⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩ : Region).Contains
      (scrP s₀ + BitVec.ofNat 64 (1024 + 8 * n)) 8 :=
    Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_stscrd hp h (o := 1024 + 8 * n) (by omega_arith) (by omega_arith) (by omega_arith)
    fun t it mt gt _ _ => k t it gt ?_ fun i hi => ?_
  · rw [mt]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc'
  · rw [mt, sd_store _ (by omega_arith) (by omega_arith) (by omega_arith), ha, hw i hi]
    by_cases e : 1024 + 8 * n = 1024 + 8 * i
    · rw [ite_eq_left e, ite_eq_left (by omega_arith), show i = n by omega_arith]
    · rw [ite_eq_right e]
      by_cases c₁ : i < n
      · rw [ite_eq_left c₁, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right c₁, ite_eq_right (by omega_arith)]

omit hp in
theorem addressHeader_eq : Impl.Argon2.RISCV64.Derive.addressHeader =
    [ld .a0 passOff, .store .d .a0 .s4 (1024 + 8 * 0), ld .a0 laneOff, .store .d .a0 .s4 (1024 + 8 * 1),
      ld .a0 sliceOff, .store .d .a0 .s4 (1024 + 8 * 2), lda .a0 14, .store .d .a0 .s4 (1024 + 8 * 3),
      ldw .a0 5, .store .d .a0 .s4 (1024 + 8 * 4), ldw .a0 0, .store .d .a0 .s4 (1024 + 8 * 5),
      ld .a0 counterOff, .store .d .a0 .s4 (1024 + 8 * 6)] := rfl

theorem aheader_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    WP isa (.block Impl.Argon2.RISCV64.Derive.addressHeader) s fun t => Inv s₀ t ∧
      (∀ r, r ≠ .a0 → t.gpr r = s.gpr r) ∧
      Frame [⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩] s.mem t.mem ∧ HW s₀ s.mem pass lane slice c 7 t.mem := by
  have fsub : ∀ r ∈ [(⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  have w₀ : HW s₀ s.mem pass lane slice c 0 s.mem := fun i _ => (ite_eq_right (Nat.not_lt_zero i)).symm
  rw [addressHeader_eq]
  refine wp_ldloc h (d := passOff) (by decide) fun s₁ u₁ => ?_
  refine hdr_step hp (n := 0) (by decide) (h.upd u₁) (by rw [u₁.gpr, ps.pass]; rfl)
    (by rw [u₁.mem]; exact w₀) fun t₁ i₁ g₁ f₁ w₁ => ?_
  refine wp_ldloc i₁ (d := laneOff) (by decide) fun s₂ u₂ => ?_
  have F₁ : Frame [⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩] s.mem t₁.mem := by rw [← u₁.mem]; exact f₁
  refine hdr_step hp (n := 1) (by decide) (i₁.upd u₂)
    (by rw [u₂.gpr, lw_keep hp F₁ fsub (by decide), ps.lane]; rfl)
    (by rw [u₂.mem]; exact w₁) fun t₂ i₂ g₂ f₂ w₂ => ?_
  have F₂ := F₁.trans (by rw [← u₂.mem]; exact f₂)
  refine wp_ldloc i₂ (d := sliceOff) (by decide) fun s₃ u₃ => ?_
  refine hdr_step hp (n := 2) (by decide) (i₂.upd u₃)
    (by rw [u₃.gpr, lw_keep hp F₂ fsub (by decide), ps.slice]; rfl)
    (by rw [u₃.mem]; exact w₂) fun t₃ i₃ g₃ f₃ w₃ => ?_
  have F₃ := F₂.trans (by rw [← u₃.mem]; exact f₃)
  refine wp_lda hp i₃ (i := 14) (by decide) fun s₄ u₄ => ?_
  refine hdr_step hp (n := 3) (by decide) (i₃.upd u₄) (by rw [u₄.gpr]; rfl)
    (by rw [u₄.mem]; exact w₃) fun t₄ i₄ g₄ f₄ w₄ => ?_
  have F₄ := F₃.trans (by rw [← u₄.mem]; exact f₄)
  refine wp_ldw hp i₄ (i := 5) (by decide) fun s₅ u₅ => ?_
  refine hdr_step hp (n := 4) (by decide) (i₄.upd u₅) (by rw [u₅.gpr]; rfl)
    (by rw [u₅.mem]; exact w₄) fun t₅ i₅ g₅ f₅ w₅ => ?_
  have F₅ := F₄.trans (by rw [← u₅.mem]; exact f₅)
  refine wp_ldw hp i₅ (i := 0) (by decide) fun s₆ u₆ => ?_
  refine hdr_step hp (n := 5) (by decide) (i₅.upd u₆) (by rw [u₆.gpr]; rfl)
    (by rw [u₆.mem]; exact w₅) fun t₆ i₆ g₆ f₆ w₆ => ?_
  have F₆ := F₅.trans (by rw [← u₆.mem]; exact f₆)
  refine wp_ldloc i₆ (d := counterOff) (by decide) fun s₇ u₇ => ?_
  refine hdr_step hp (n := 6) (by decide) (i₆.upd u₇)
    (by rw [u₇.gpr, lw_keep hp F₆ fsub (by decide), hc]; rfl)
    (by rw [u₇.mem]; exact w₆) fun t i g f w => WP.block_nil ⟨i, fun r a => ?_,
      F₆.trans (by rw [← u₇.mem]; exact f), w⟩
  rw [g, u₇.other _ a, g₆, u₆.other _ a, g₅, u₅.other _ a, g₄, u₄.other _ a, g₃, u₃.other _ a, g₂,
    u₂.other _ a, g₁, u₁.other _ a]

omit hp in
/-- A doubleword of `scratch` outside a frame's region of `scratch`. -/
theorem sd_frame {m m' : Mem} {a n : Nat} (f : Frame [⟨scrP s₀ + BitVec.ofNat 64 a, n⟩] m m') {o : Nat}
    (h : o + 8 ≤ a ∨ a + n ≤ o) (ho : o + 8 ≤ 16384) (hn : a + n ≤ 16384) : sd s₀ m' o = sd s₀ m o := by
  refine f.readW (r := ⟨scrP s₀ + BitVec.ofNat 64 o, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ h (by omega_arith) (by omega_arith)

theorem input_words {pass lane slice c : Nat} :
    (Vector.ofFn fun j : Fin 128 => if j.val < 7 then hdr s₀ pass lane slice c j.val else 0) =
      Proof.Argon2.addressInput (prm s₀) pass lane slice c := by
  have eb : arg s₀ 14 = BitVec.ofNat 64 (prm s₀).blocks := by rw [← hp.blocks]; simp
  have ep : (arg32 s₀ 5).setWidth 64 = BitVec.ofNat 64 (prm s₀).passes := ofNat_toNat (toNat_ext32 _)
  have ek : (arg32 s₀ 0).setWidth 64 = BitVec.ofNat 64 (prm s₀).variant.code := by
    rw [variant_code hp.kind_le]; exact ofNat_toNat (toNat_ext32 _)
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Proof.Argon2.addressInput, Vector.getElem_set, zeroBlock,
    Vector.getElem_replicate]
  rcases (by omega_arith : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ 7 ≤ j) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | hj7
  · simp [hdr]
  · simp [hdr]
  · simp [hdr]
  · simp [hdr, eb]
  · simp [hdr, ep]
  · simp [hdr, ek]
  · simp [hdr]
  · rw [ite_eq_right (by omega_arith)]
    simp (disch := omega_arith) only [ite_eq_right]

/-- The address-generation input block at `scratch + 1024`, and a zero block at `scratch + 3072`. -/
theorem input_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.clearAt .s4 1024 ++ Impl.Argon2.RISCV64.Derive.clearAt .s0 1024 ++
      Impl.Argon2.RISCV64.Derive.addressHeader)) s fun t => Inv s₀ t ∧
      (∀ r, r ≠ .a0 → t.gpr r = s.gpr r) ∧
      Frame [⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩, ⟨scrP s₀ + BitVec.ofNat 64 3072, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 1024) = Proof.Argon2.addressInput (prm s₀) pass lane slice c ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 3072) = zeroBlock := by
  have fsub : ∀ d, d + 1024 ≤ 16384 → ∀ r ∈ [(⟨scrP s₀ + BitVec.ofNat 64 d, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀], Region.Sub r r' := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Offset.sub_base _ hd⟩
  rw [List.append_assoc]
  refine clearAt_ok hp h (b := .s4) (by decide) (B := 0) (by rw [h.s4]; simp) (d := 1024) (by decide)
    (by decide) (by decide) fun t₁ i₁ g₁ f₁ z₁ => ?_
  refine clearAt_ok hp i₁ (b := .s0) (by decide) (B := 2048) i₁.s0 (d := 1024) (by decide)
    (by decide) (by decide) fun t₂ i₂ g₂ f₂ z₂ => ?_
  simp only [Nat.zero_add, show 2048 + 1024 = 3072 from rfl] at f₁ z₁ f₂ z₂
  have L : ∀ d, d + 8 ≤ 320 → lw s₀ t₂ d = lw s₀ s d := fun d h₂ => by
    rw [lw_keep hp f₂ (fsub _ (by decide)) h₂, lw_keep hp f₁ (fsub _ (by decide)) h₂]
  refine (aheader_ok hp i₂ (pass := pass) (slice := slice) (lane := lane) (index := index) (c := c)
    (ps.of_lw fun d h₁ h₂ => L d (by omega_arith)) (by rw [L _ (by decide)]; exact hc)).mono
    fun t ⟨it, gt, ft, wt⟩ => ⟨it, fun r a => by rw [gt r a, g₂ r a, g₁ r a], ?_, ?_, ?_⟩
  · refine (Frame.trans (f₁.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
      (f₂.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)).trans
      (ft.sub fun r hr => ⟨⟨scrP s₀ + BitVec.ofNat 64 1024, 1024⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  · rw [blockAt_of_sd (f := fun i => if i < 7 then hdr s₀ pass lane slice c i else 0) fun i hi => ?_,
      input_words hp]
    rw [wt i hi]
    by_cases e : i < 7
    · rw [ite_eq_left e, ite_eq_left e]
    · rw [ite_eq_right e, ite_eq_right e, sd_frame f₂ (by omega_arith) (by omega_arith) (by decide)]
      exact z₁ i hi
  · rw [blockAt_of_sd (f := fun _ => 0) fun i hi => ?_]
    · apply Vector.ext; intro j hj; simp [zeroBlock]
    rw [sd_frame ft (by omega_arith) (by omega_arith) (by decide)]
    exact z₂ i hi

end

end VG.Proof.Argon2.RISCV64.Derive
