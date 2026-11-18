module

import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillCall
public import VerifiedGarbage.Proof.Argon2.FillStep
import VerifiedGarbage.Proof.Argon2.FillPositions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Initial
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.MemoryInit
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.FillDep
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.AddressInput

/-! ### `Argon2.PPC64LE.Derive.FillInput`, which this module and modules that import it used -/

section

/-!
# Argon2 on PPC64LE: the address-generation input block

`input_ok`: `clearAt 5120`, `clearAt 7168` and `addressHeader` leave the
input block of §3.4.1.2 (`Proof.Argon2.addressInput`) at `scratch + 5120`
and a zero block at `scratch + 7168`, writing only those two blocks.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_li)
open VG.Spec.Argon2 (Block zeroBlock)
open VG.Impl.Argon2.PPC64LE.Derive (passOff laneOff sliceOff counterOff ld lda ldw)

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

/-- `n` stores of `r3 = 0` to `r31 + d + 8k`. -/
theorem zeros_ok {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 1024 ≤ 8192) (hd8 : d % 8 = 0)
    (ha : s.gpr .r3 = 0) :
    ∀ n ≤ 128, WP isa (.block ((List.range n).map fun k => Instr.store .d .r3 .r31 (d + 8 * k))) s
      fun t => Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨scrP s₀ + BitVec.ofNat 64 d, 1024⟩] s.mem t.mem ∧
        ∀ i < n, sd s₀ t.mem (d + 8 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((zeros_ok h hd hd8 ha n (by omega_arith)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have hc' : (⟨scrP s₀ + BitVec.ofNat 64 d, 1024⟩ : Region).Contains
        (scrP s₀ + BitVec.ofNat 64 (d + 8 * n)) 8 :=
      Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
    refine wp_stscrd hp it (o := d + 8 * n) (by omega_arith) (by omega_arith) (by omega_arith)
      fun t₁ i₁ m₁ g₁ _ _ => WP.block_nil ⟨i₁, by rw [g₁, gt], ?_, fun i hi => ?_⟩
    · rw [m₁]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [m₁, gt, ha, sd_store _ (by omega_arith) (by omega_arith) (by omega_arith)]
      by_cases e : d + 8 * n = d + 8 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact wt i (by omega_arith)

/-- `clearAt d`: zero `scratch[d, d + 1024)`. -/
theorem clearAt_ok {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 1024 ≤ 8192) (hd8 : d % 8 = 0)
    {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ r, r ≠ .r3 → t.gpr r = s.gpr r) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 d, 1024⟩] s.mem t.mem → (∀ i < 128, sd s₀ t.mem (d + 8 * i) = 0) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.clearAt d ++ is)) s Q := by
  unfold Impl.Argon2.PPC64LE.Derive.clearAt
  simp only [List.cons_append]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁
  refine WP.block_append ((zeros_ok hp i₁ hd hd8 u₁.gpr 128 (Nat.le_refl _)).mono fun t ⟨it, gt, ft, wt⟩ =>
    k t it (fun r a => ?_) ?_ wt)
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
  ∀ i < 128, sd s₀ m' (5120 + 8 * i) = if i < n then hdr s₀ pass lane slice c i else sd s₀ m (5120 + 8 * i)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One doubleword of the header. -/
theorem hdr_step {m : Mem} {pass lane slice c n : Nat} (hn : n < 7) {u : State} (h : Inv s₀ u)
    (ha : u.gpr .r3 = hdr s₀ pass lane slice c n) (hw : HW s₀ m pass lane slice c n u.mem)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.gpr = u.gpr → Frame [⟨scrP s₀ + BitVec.ofNat 64 5120, 1024⟩] u.mem t.mem →
      HW s₀ m pass lane slice c (n + 1) t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store .d .r3 .r31 (5120 + 8 * n) :: is)) u Q := by
  have hc' : (⟨scrP s₀ + BitVec.ofNat 64 5120, 1024⟩ : Region).Contains
      (scrP s₀ + BitVec.ofNat 64 (5120 + 8 * n)) 8 :=
    Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine wp_stscrd hp h (o := 5120 + 8 * n) (by omega_arith) (by omega_arith) (by omega_arith)
    fun t it mt gt _ _ => k t it gt ?_ fun i hi => ?_
  · rw [mt]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc'
  · rw [mt, sd_store _ (by omega_arith) (by omega_arith) (by omega_arith), ha, hw i hi]
    by_cases e : 5120 + 8 * n = 5120 + 8 * i
    · rw [ite_eq_left e, ite_eq_left (by omega_arith), show i = n by omega_arith]
    · rw [ite_eq_right e]
      by_cases c₁ : i < n
      · rw [ite_eq_left c₁, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right c₁, ite_eq_right (by omega_arith)]

omit hp in
theorem addressHeader_eq : Impl.Argon2.PPC64LE.Derive.addressHeader =
    [ld .r3 passOff, .store .d .r3 .r31 (5120 + 8 * 0), ld .r3 laneOff, .store .d .r3 .r31 (5120 + 8 * 1),
      ld .r3 sliceOff, .store .d .r3 .r31 (5120 + 8 * 2), lda .r3 14, .store .d .r3 .r31 (5120 + 8 * 3),
      ldw .r3 5, .store .d .r3 .r31 (5120 + 8 * 4), ldw .r3 0, .store .d .r3 .r31 (5120 + 8 * 5),
      ld .r3 counterOff, .store .d .r3 .r31 (5120 + 8 * 6)] := rfl

theorem aheader_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    WP isa (.block Impl.Argon2.PPC64LE.Derive.addressHeader) s fun t => Inv s₀ t ∧
      (∀ r, r ≠ .r3 → t.gpr r = s.gpr r) ∧
      Frame [⟨scrP s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t.mem ∧ HW s₀ s.mem pass lane slice c 7 t.mem := by
  have fsub : ∀ r ∈ [(⟨scrP s₀ + BitVec.ofNat 64 5120, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  have w₀ : HW s₀ s.mem pass lane slice c 0 s.mem := fun i _ => (ite_eq_right (Nat.not_lt_zero i)).symm
  rw [addressHeader_eq]
  refine wp_ldloc h (d := passOff) (by decide) fun s₁ u₁ => ?_
  refine hdr_step hp (n := 0) (by decide) (h.upd u₁) (by rw [u₁.gpr, ps.pass]; rfl)
    (by rw [u₁.mem]; exact w₀) fun t₁ i₁ g₁ f₁ w₁ => ?_
  refine wp_ldloc i₁ (d := laneOff) (by decide) fun s₂ u₂ => ?_
  have F₁ : Frame [⟨scrP s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₁.mem := by rw [← u₁.mem]; exact f₁
  refine hdr_step hp (n := 1) (by decide) (i₁.upd u₂)
    (by rw [u₂.gpr, lw_keep hp F₁ fsub (by decide) (by decide), ps.lane]; rfl)
    (by rw [u₂.mem]; exact w₁) fun t₂ i₂ g₂ f₂ w₂ => ?_
  have F₂ := F₁.trans (by rw [← u₂.mem]; exact f₂)
  refine wp_ldloc i₂ (d := sliceOff) (by decide) fun s₃ u₃ => ?_
  refine hdr_step hp (n := 2) (by decide) (i₂.upd u₃)
    (by rw [u₃.gpr, lw_keep hp F₂ fsub (by decide) (by decide), ps.slice]; rfl)
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
    (by rw [u₇.gpr, lw_keep hp F₆ fsub (by decide) (by decide), hc]; rfl)
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

/-- The address-generation input block at `scratch + 5120`, and a zero block at `scratch + 7168`. -/
theorem input_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.clearAt 5120 ++ Impl.Argon2.PPC64LE.Derive.clearAt 7168 ++
      Impl.Argon2.PPC64LE.Derive.addressHeader)) s fun t => Inv s₀ t ∧
      (∀ r, r ≠ .r3 → t.gpr r = s.gpr r) ∧
      Frame [⟨scrP s₀ + BitVec.ofNat 64 5120, 1024⟩, ⟨scrP s₀ + BitVec.ofNat 64 7168, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 5120) = Proof.Argon2.addressInput (prm s₀) pass lane slice c ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 7168) = zeroBlock := by
  have fsub : ∀ d, d + 1024 ≤ 16384 → ∀ r ∈ [(⟨scrP s₀ + BitVec.ofNat 64 d, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Offset.sub_base _ hd⟩
  rw [List.append_assoc]
  refine clearAt_ok hp h (d := 5120) (by decide) (by decide) fun t₁ i₁ g₁ f₁ z₁ => ?_
  refine clearAt_ok hp i₁ (d := 7168) (by decide) (by decide) fun t₂ i₂ g₂ f₂ z₂ => ?_
  have L : ∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t₂ d = lw s₀ s d := fun d h₁ h₂ => by
    rw [lw_keep hp f₂ (fsub _ (by decide)) h₁ h₂, lw_keep hp f₁ (fsub _ (by decide)) h₁ h₂]
  refine (aheader_ok hp i₂ (pass := pass) (slice := slice) (lane := lane) (index := index) (c := c)
    (ps.of_lw fun d h₁ h₂ => L d (by omega_arith) (by omega_arith)) (by rw [L _ (by decide) (by decide)]; exact hc)).mono
    fun t ⟨it, gt, ft, wt⟩ => ⟨it, fun r a => by rw [gt r a, g₂ r a, g₁ r a], ?_, ?_, ?_⟩
  · refine (Frame.trans (f₁.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
      (f₂.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)).trans
      (ft.sub fun r hr => ⟨⟨scrP s₀ + BitVec.ofNat 64 5120, 1024⟩, by simp, by
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

end VG.Proof.Argon2.PPC64LE.Derive

end

end

/-!
# Argon2 on PPC64LE: the address block

`addressCalls_ok`: the address block, G(0, G(0, input)), at `scratch + 6144`.
`addressCache_ok`: J₁, J₂ from the cached address block, regenerated when
the index enters a new group of 128. `randomSource_ok`: J₁, J₂ are the
random word of `FillStep.random`.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_add wp_addi wp_sub wp_li wp_lsl wp_lsr wp_and wp_mov wp_lwz)
open VG.Spec.Argon2 (Block zeroBlock FillState compress addressBlock)
open VG.Proof.Argon2 (matrixCell Represents)
open VG.Impl.Argon2.PPC64LE.Derive (indexOff counterOff j1Off j2Off)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `stage x y out`: G of the blocks at `scratch + x` and `scratch + y` to `scratch + out`. -/
theorem stage_ok {s : State} (h : Inv s₀ s) {x y o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 8192)
    (hx : 4096 ≤ x) (hx' : x + 1024 ≤ 8192) (hxo : x + 1024 ≤ o ∨ o + 1024 ≤ x)
    (hy : 4096 ≤ y) (hy' : y + 1024 ≤ 8192) (hyo : y + 1024 ≤ o ∨ o + 1024 ≤ y) :
    WP isa (Impl.Argon2.PPC64LE.Derive.stage x y o) s fun t => Inv s₀ t ∧
      (∀ q ∈ preserved, t.gpr q = s.gpr q) ∧
      Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩] s.mem t.mem ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 o) =
        compress (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 x)) (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 y)) := by
  unfold Impl.Argon2.PPC64LE.Derive.stage
  refine WP.seq (wp_addi (by omega_arith) fun s₁ u₁ => wp_addi (by omega_arith) fun s₂ u₂ =>
    wp_addi (by omega_arith) fun s₃ u₃ => wp_mov fun s₄ u₄ => WP.block_nil ?_)
  have o₄ := (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
  have i₄ := h.only o₄
  have r31 : s.gpr .r31 = scrP s₀ := h.r31
  have dx : s₄.gpr .r6 = scrP s₀ := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r31]
  have ax : s₄.gpr .r3 = scrP s₀ + BitVec.ofNat 64 x := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, r31]
  have sx : s₄.gpr .r4 = scrP s₀ + BitVec.ofNat 64 y := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), r31]
  have cx : s₄.gpr .r5 = scrP s₀ + BitVec.ofNat 64 o := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r31]
  refine ccall_ok hp i₄ dx ho (by omega_arith) cx (by rw [ax]; exact .inr ⟨x, hx, by omega_arith, hxo, rfl⟩)
    (by rw [sx]; exact .inr ⟨y, hy, by omega_arith, hyo, rfl⟩) fun t it cs f post =>
      ⟨it, fun q hq => ?_, by rw [← o₄.mem]; exact f, by rw [post, ax, sx, o₄.mem]⟩
  rw [cs q hq]
  exact o₄.gpr q fun hm => by revert hq; revert hm; revert q; decide

omit hp in
/-- A block of `scratch` at `d`, outside the regions G's call at `o` writes. -/
theorem stage_keep {m m' : Mem} {o : Nat} (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩] m m') {d : Nat} (hd : 4096 ≤ d)
    (hd' : d + 1024 ≤ 16384) (hdo : d + 1024 ≤ o ∨ o + 1024 ≤ d) :
    blockAt m' (scrP s₀ + BitVec.ofNat 64 d) = blockAt m (scrP s₀ + BitVec.ofNat 64 d) := by
  refine blockAt_keep f fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ hdo (by omega_arith) (by omega_arith)
  · exact Offset.disjoint_base _ hd (by omega_arith)

omit hp in
theorem stage_frame {m m' : Mem} {o : Nat} (ho' : o + 1024 ≤ 16384)
    (f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrP s₀, 4096⟩] m m') :
    Frame [scrR s₀] m m' :=
  f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ ho'⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩

/-- `addressCalls`: the address block for the counter `c` at `scratch + 6144`. -/
theorem addressCalls_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    WP isa Impl.Argon2.PPC64LE.Derive.addressCalls s fun t => Inv s₀ t ∧
      (∀ q ∈ preserved, t.gpr q = s.gpr q) ∧ Frame [scrR s₀] s.mem t.mem ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 6144) = addressBlock (prm s₀) pass lane slice c := by
  unfold Impl.Argon2.PPC64LE.Derive.addressCalls
  refine WP.seq ((input_ok hp h ps hc).mono fun t₁ ⟨i₁, g₁, f₁, b₁, z₁⟩ => ?_)
  refine WP.seq ((stage_ok hp i₁ (x := 7168) (y := 5120) (o := 4096) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mono fun t₂ ⟨i₂, g₂, f₂, b₂⟩ => ?_)
  refine (stage_ok hp i₂ (x := 7168) (y := 4096) (o := 6144) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mono
    fun t ⟨it, gt, ft, bt⟩ => ⟨it, fun q hq => ?_, ?_, ?_⟩
  · rw [gt q hq, g₂ q hq]
    exact g₁ q fun e => by subst e; exact absurd hq (by decide)
  · refine Frame.trans (f₁.sub fun r hr => ?_) ((stage_frame (by decide) f₂).trans (stage_frame (by decide) ft))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  · rw [bt, stage_keep (by decide) f₂ (d := 7168) (by decide) (by decide) (by decide), b₂, z₁, b₁]
    rfl

end

theorem and127 {n : Nat} (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& BitVec.ofNat 64 127 = BitVec.ofNat 64 (n % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (a := 127) (by decide), Nat.mod_eq_of_lt (a := n % 128) (by omega_arith),
    show 127 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shr7 {n : Nat} (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 7 = BitVec.ofNat 64 (n / 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `cacheWord`: J₁ and J₂ are doubleword `index mod 128` of the cached address block. -/
theorem cacheWord_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < 2 ^ 30) :
    WP isa (.block Impl.Argon2.PPC64LE.Derive.cacheWord) s fun t => FS s₀ pass slice lane index ctr st t ∧
      Rand s₀ t ((blockAt s.mem (scrP s₀ + BitVec.ofNat 64 6144))[index % 128]'(Nat.mod_lt _ (by decide))) := by
  have e8 : 8 * (index % 128) < 1024 := by omega_arith
  unfold Impl.Argon2.PPC64LE.Derive.cacheWord
  refine wp_ldloc h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ =>
    wp_and fun s₃ u₃ => wp_lsl (by decide) fun s₄ u₄ => wp_add fun s₅ u₅ => ?_
  have o₅ := (((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
    (Only.of_upd u₄)).trans (Only.of_upd u₅))
  have h₅ := h.of_only o₅
  have a₅ : s₅.gpr .r3 = scrP s₀ + BitVec.ofNat 64 (8 * (index % 128)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.inv.r31, u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr,
      h.pos.index, and127 (by omega_arith), ofNat_shl' (by omega_arith)]
    congr 2; omega_arith
  have m₅ : s₅.mem = s.mem := o₅.mem
  have inS : ∀ t : State, Inv s₀ t → ∀ o, o + 4 ≤ 1024 →
      InRegions (t.rd ++ t.wr) (scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + o)) 4 :=
    fun t it o ho => by
      rw [it.wr]
      exact ⟨scrR s₀, List.mem_append_right _ (scr_mem hp), Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have ad : ∀ o, s₅.gpr .r3 + BitVec.ofNat 64 (6144 + o) =
      scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + o) := fun o => by
    rw [a₅, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega_arith
  refine wp_lwz (a := scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 0)) (by decide) (ad 0)
    (inS _ h₅.inv 0 (by decide)) fun s₆ u₆ => ?_
  have h₆ := h₅.of_only (Only.of_upd u₆)
  refine wp_stloc h₆.inv (d := j1Off) (by decide) fun s₇ i₇ v₇ o₇ g₇ m₇ => ?_
  have h₇ := h₆.store hp i₇ (d := j1Off) (by decide) (by decide) m₇
  refine wp_lwz (a := scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 4)) (by decide)
    (by rw [g₇, u₆.other _ (by decide)]; exact ad 4) (inS _ h₇.inv 4 (by decide)) fun s₈ u₈ => ?_
  have h₈ := h₇.of_only (Only.of_upd u₈)
  refine wp_stloc h₈.inv (d := j2Off) (by decide) fun t it vt ot gt mt => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact h₈.store hp it (d := j2Off) (by decide) (by decide) mt
  · have w0 : s.mem.readW (scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 0)) 64 =
        (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 6144))[index % 128] := by
      rw [Nat.add_zero, blockAt_get _ _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [ot j1Off (by decide) (by decide), lw_mem u₈.mem, v₇, u₆.gpr, m₅, Mem.readW_lo32 w0, lo_ext]
  · have w0 : s₇.mem.readW (scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 0)) 64 =
        (blockAt s.mem (scrP s₀ + BitVec.ofNat 64 6144))[index % 128] := by
      rw [m₇, (frame_loc _).readW (r := ⟨scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 0), 8⟩)
        (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (loc_scr hp (by decide) (by decide) (by omega_arith)).symm) (by decide),
        u₆.mem, m₅, Nat.add_zero, blockAt_get _ _ (Nat.mod_lt _ (by decide)), BitVec.add_assoc,
        BitVec.ofNat_add_ofNat]
    have e4 : scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 4) =
        scrP s₀ + BitVec.ofNat 64 (6144 + 8 * (index % 128) + 0) + BitVec.ofNat 64 4 := by
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    rw [vt, u₈.gpr, e4]
    exact (congrArg (BitVec.setWidth 64) (Mem.readW_hi32 w0)).trans (hi_ext _)

omit hp in
/-- The cached address block is that of `c`. -/
theorem cached {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 32)
    (he : lw s₀ s counterOff = BitVec.ofNat 64 c) :
    blockAt s.mem (scrP s₀ + BitVec.ofNat 64 6144) = addressBlock (prm s₀) pass lane slice c := by
  obtain ⟨c0, c1, c2 | ⟨_, c4⟩⟩ := h.cache
  · rw [he, c2] at c1
    have := congrArg BitVec.toNat c1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    exact absurd this (by simp; omega_arith)
  · rw [c4]
    rw [he] at c1
    have := congrArg BitVec.toNat c1
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)] at this
    rw [this]

/-- `cacheCheck`: `r3 :=` the counter of the index's group; `r4` is zero if it is cached. -/
theorem cacheCheck_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen) :
    WP isa (.block Impl.Argon2.PPC64LE.Derive.cacheCheck) s fun t => FS s₀ pass slice lane index ctr st t ∧
      t.gpr .r3 = BitVec.ofNat 64 (index / 128 + 1) ∧
      VG.PPC64LE.eval (.zero .d .r4) t =
        some (BitVec.ofNat 64 (index / 128 + 1) - lw s₀ t counterOff == 0) := by
  have sl := segLen_lt hp
  unfold Impl.Argon2.PPC64LE.Derive.cacheCheck
  refine wp_ldloc h.inv (d := indexOff) (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ =>
    wp_addi (by decide) fun s₃ u₃ => ?_
  have o₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)
  have h₃ := h.of_only o₃
  have a₃ : s₃.gpr .r3 = BitVec.ofNat 64 (index / 128 + 1) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, h.pos.index, shr7 (by omega_arith), BitVec.ofNat_add_ofNat]
  refine wp_ldloc h₃.inv (d := counterOff) (by decide) fun s₄ u₄ => wp_sub fun t u => WP.block_nil ?_
  have o₄ := (Only.of_upd u₄).trans (Only.of_upd u)
  refine ⟨h₃.of_only o₄, by rw [u.other _ (by decide), u₄.other _ (by decide), a₃], ?_⟩
  rw [MdStream.PPC64LE.eval_zero, u.gpr, u₄.other _ (by decide), a₃, u₄.gpr, lw_mem u.mem,
    lw_mem u₄.mem]

/-- The address block of the index's group, regenerated unless it is cached. -/
theorem cacheFill_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h₄ : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen)
    (a₃ : s.gpr .r3 = BitVec.ofNat 64 (index / 128 + 1))
    (z₄ : VG.PPC64LE.eval (.zero .d .r4) s =
      some (BitVec.ofNat 64 (index / 128 + 1) - lw s₀ s counterOff == 0)) :
    WP isa (.ite (.zero .d .r4) (.block []) (.seq (.block [Impl.Argon2.PPC64LE.Derive.st counterOff .r3])
      Impl.Argon2.PPC64LE.Derive.addressCalls)) s fun t =>
      FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      blockAt t.mem (scrP s₀ + BitVec.ofNat 64 6144) = addressBlock (prm s₀) pass lane slice (index / 128 + 1) := by
  have sl := segLen_lt hp
  refine WP.ite (BitVec.ofNat 64 (index / 128 + 1) - lw s₀ s counterOff == 0) z₄
    (fun hb => ?_) fun hb => ?_
  · have ce : lw s₀ s counterOff = BitVec.ofNat 64 (index / 128 + 1) := by
      have e := beq_iff_eq.mp hb
      exact ((BitVec.sub_eq_iff_eq_add.mp e).trans (by simp)).symm
    have cb := cached h₄ (c := index / 128 + 1) (by omega_arith) (by omega_arith) ce
    exact WP.block_nil ⟨⟨h₄.inv, h₄.pr, h₄.pos, ⟨by omega_arith, ce, .inr ⟨by omega_arith, cb⟩⟩, h₄.mem⟩, cb⟩
  · refine WP.seq (wp_stloc h₄.inv (d := counterOff) (by decide) fun s₅ i₅ v₅ o₅ g₅ m₅ => WP.block_nil ?_)
    have L₅ : ∀ d, 208 ≤ d → d + 8 ≤ 272 → (d + 8 ≤ counterOff ∨ counterOff + 8 ≤ d) →
        lw s₀ s₅ d = lw s₀ s d := fun d h₁ h₂ h₃ => o₅ d (by omega_arith) (by
          simp only [counterOff] at h₃ ⊢; omega_arith)
    have P₅ : Pos s₀ s₅ pass slice lane index :=
      ⟨by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.pass,
        by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.slice,
        by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.lane,
        by rw [L₅ _ (by decide) (by decide) (by decide)]; exact h₄.pos.index⟩
    refine (addressCalls_ok hp i₅ (index := index) (c := index / 128 + 1) P₅ (by rw [v₅, a₃])).mono
      fun t ⟨it, _, ft, bt⟩ => ⟨?_, bt⟩
    have fsub : ∀ r ∈ [scrR s₀], ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
    have Lt : ∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t d = lw s₀ s₅ d := fun d h₁ h₂ =>
      lw_keep hp ft fsub h₁ h₂
    refine ⟨it, Prm.of_lw h₄.pr fun d h₁ h₂ => ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨by omega_arith,
      by rw [Lt _ (by decide) (by decide), v₅, a₃], .inr ⟨by omega_arith, bt⟩⟩, Represents.keep h₄.mem fun k hk => ?_⟩
    · rw [Lt d (by omega_arith) (by omega_arith), L₅ d (by omega_arith) (by omega_arith) (by simp only [counterOff]; omega_arith)]
    · rw [Lt _ (by decide) (by decide)]; exact P₅.pass
    · rw [Lt _ (by decide) (by decide)]; exact P₅.slice
    · rw [Lt _ (by decide) (by decide)]; exact P₅.lane
    · rw [Lt _ (by decide) (by decide)]; exact P₅.index
    · have hk' : k < blocksN s₀ := by rw [hp.blocks]; exact hk
      have sk := Proof.Argon2.matrixCell_sub (memP s₀) _ _ hk'
      rw [blockAt_keep ft fun r hr => ?_, m₅, blockAt_keep (frame_loc _) fun r hr => ?_]
      · simp only [List.mem_singleton] at hr; subst hr
        exact (loc_disj hp (d := counterOff) (by decide) (by decide) (memR s₀) (by simp)).symm.sub_left sk
      · simp only [List.mem_singleton] at hr; subst hr
        exact hp.mem_scr.sub_left sk

/-- `addressCache`: J₁ and J₂ from the address block of the index's group of 128. -/
theorem addressCache_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.PPC64LE.Derive.addressCache s fun t =>
      FS s₀ pass slice lane index (index / 128 + 1) st t ∧
      Rand s₀ t ((addressBlock (prm s₀) pass lane slice (index / 128 + 1))[index % 128]'(Nat.mod_lt _ (by decide))) := by
  have sl := segLen_lt hp
  unfold Impl.Argon2.PPC64LE.Derive.addressCache
  refine WP.seq ((cacheCheck_ok hp h hi).mono fun s₄ ⟨h₄, a₄, z₄⟩ => ?_)
  refine WP.seq ((cacheFill_ok hp h₄ hi a₄ z₄).mono fun t ⟨ht, bt⟩ =>
    (cacheWord_ok hp ht (by omega_arith)).mono fun u ⟨hu, wu⟩ => ⟨hu, ?_⟩)
  rw [bt] at wu
  exact wu

/-- `randomSource`: J₁ and J₂ are the step's random word. -/
theorem randomSource_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀)
    (hs : slice < 4) (hi : index < (prm s₀).segmentLen) :
    WP isa Impl.Argon2.PPC64LE.Derive.randomSource s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr) st t ∧
      Rand s₀ t (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) := by
  unfold Impl.Argon2.PPC64LE.Derive.randomSource
  refine WP.seq ((addressMode_ok hp h.inv h.pos hpass hs).mono fun s₁ ⟨z₁, k₁⟩ => ?_)
  have h₁ := h.of_only k₁
  refine WP.ite (!Spec.Argon2.independent (prm s₀) pass slice) z₁ (fun hb => ?_) fun hb => ?_
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = false := by simpa using hb
    refine (dependentWord_ok hp h₁ hl hs hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [ctrNext, hind]; exact ht, ?_⟩
    have cl := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
      (column := slice * (prm s₀).segmentLen + index) hl
    rw [k₁.mem, h.mem.block _ cl] at wt
    rw [Proof.Argon2.FillStep.random, hind]
    simpa only [Bool.false_eq_true, ite_false] using wt
  · have hind : Spec.Argon2.independent (prm s₀) pass slice = true := by simpa using hb
    refine (addressCache_ok hp h₁ hi).mono fun t ⟨ht, wt⟩ => ⟨by rw [ctrNext, hind]; exact ht, ?_⟩
    rw [Proof.Argon2.FillStep.random, hind]
    simpa only [ite_true] using wt

end

end VG.Proof.Argon2.PPC64LE.Derive
