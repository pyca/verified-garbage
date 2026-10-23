module

public import VerifiedGarbage.Proof.Idea.PPC64LE.Round
public import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# IDEA on PPC64LE: a block

`cryptBlock_ok`: `Impl.Idea.PPC64LE.cryptBlock` replaces the block at `r4`
with `Spec.Idea.cryptBlock` of it under the subkeys at `r3`: the block's
words are loaded a byte at a time (`load_ok`), run through the rounds
(`rounds_ok`) and the output transformation (`output_ok`), and stored a
byte at a time (`store_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.PPC64LE

open VG VG.PPC64LE VG.Impl.Idea.PPC64LE

/-! ## Loading -/

theorem loadWord_ok {r : Reg} (hr : r ≠ .r11 ∧ r ≠ .r4) (k : Nat) (hk : k < 4) (s : State) {a : Addr}
    (ha : s.gpr .r4 = a)
    (h0 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k)) 1)
    (h1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k + 1)) 1) :
    WP isa (.block (loadWord r k)) s fun t =>
      t.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++ s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.r11, r] s t := by
  refine WP.mono (WP.keep (c := .block (loadWord r k)) [.r11, r] (Q := fun t =>
      t.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++
        s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      t.mem = s.mem) ?_ (by simp [writesOnly, Code.allInstrs_eq, instrs, loadWord, dstOf]) rfl)
    fun t ⟨⟨h₁, h₂⟩, hk⟩ => ⟨h₁, h₂, hk⟩
  unfold loadWord
  irun [ha, h0, h1, hr.1, Ne.symm hr.1, hr.2, Ne.symm hr.2, show 2 * k < 2 ^ 15 by omega, show 2 * k + 1 < 2 ^ 15 by omega]
  exact bytes16 _ _

/-- The bytes of the block at `a` can be read. -/
def BlockRead (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 i) 1

theorem BlockRead.keep {rs : List Reg} {s s' : State} {a : Addr} (h : BlockRead s a)
    (hk : Keep rs s s') : BlockRead s' a := by
  intro i hi; rw [hk.2.1, hk.2.2]; exact h i hi

theorem load_ok (s : State) {a : Addr} (ha : s.gpr .r4 = a) (hb : BlockRead s a) :
    WP isa (.block load) s fun t =>
      Holds (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem a)) t ∧ t.mem = s.mem ∧
      Keep [.r11, .r6, .r7, .r8, .r9] s t := by
  have w (k : Nat) (hk : k < 4) := decodeBlock_blockAt s.mem a hk
  simp only [load, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .r6) (by decide) 0 (by decide) s ha (hb _ (by decide))
    (hb _ (by decide))) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .r7) (by decide) 1 (by decide) s₁ ((e₁.gpr (by decide)).trans ha)
    ((hb.keep e₁) _ (by decide)) ((hb.keep e₁) _ (by decide))) fun s₂ ⟨v₂, m₂, e₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .r8) (by decide) 2 (by decide) s₂
    ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans ha))
    ((hb.keep e₁ |>.keep e₂) _ (by decide)) ((hb.keep e₁ |>.keep e₂) _ (by decide)))
    fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  refine WP.mono (loadWord_ok (r := .r9) (by decide) 3 (by decide) s₃
    ((e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans ha)))
    ((hb.keep e₁ |>.keep e₂ |>.keep e₃) _ (by decide)) ((hb.keep e₁ |>.keep e₂ |>.keep e₃) _ (by decide)))
    fun s₄ ⟨v₄, m₄, e₄⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by rw [m₄, m₃, m₂, m₁], (((e₁.trans e₂).trans e₃).trans e₄).mono (by decide)⟩
  · rw [e₄.gpr (by decide), e₃.gpr (by decide), e₂.gpr (by decide), v₁, w 0 (by decide)]
  · rw [e₄.gpr (by decide), e₃.gpr (by decide), v₂, m₁, w 1 (by decide)]
  · rw [e₄.gpr (by decide), v₃, m₂, m₁, w 2 (by decide)]
  · rw [v₄, m₃, m₂, m₁, w 3 (by decide)]

/-! ## The rounds -/

theorem rounds_ok (z : Spec.Idea.Schedule) (x : Spec.Idea.State) :
    ∀ n ≤ 8, ∀ s : State, Holds x s → KeyOk z s →
      WP isa (.block ((List.range n).flatMap round)) s fun t =>
        Holds (roundsSpec z n x) t ∧ t.mem = s.mem ∧ Keep roundWrites s t
  | 0, _, s, hx, _ => WP.block_nil ⟨hx, rfl, Keep.refl _ _⟩
  | n + 1, hn, s, hx, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (rounds_ok z x n (by omega) s hx hk) fun s₁ ⟨x₁, m₁, e₁⟩ => ?_
    refine WP.mono (round_ok n (by omega) z _ s₁ x₁ (hk.keep e₁ m₁ (by decide) (by decide)))
      fun s₂ ⟨x₂, m₂, e₂⟩ => ⟨?_, m₂.trans m₁, (e₁.trans e₂).mono (by decide)⟩
    simp only [roundsSpec, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact x₂

/-! ## The output transformation -/

/-- The output words: `Y₁` in `r6`, `Y₂` in `r8`, `Y₃` in `r7`, `Y₄` in `r9`. -/
structure OutHolds (y : Spec.Idea.State) (s : State) : Prop where
  r6 : s.gpr .r6 = (y.getD 0 0).setWidth 64
  r8 : s.gpr .r8 = (y.getD 1 0).setWidth 64
  r7 : s.gpr .r7 = (y.getD 2 0).setWidth 64
  r9 : s.gpr .r9 = (y.getD 3 0).setWidth 64

theorem hi16 (x : BitVec 32) : ((x.setWidth 64 >>> 16).setWidth 16) = (x >>> 16).setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64)]

theorem out1_ok (s : State) (hk : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 100) 4) :
    WP isa (.block [mov .r11 .r9, .load .w .r12 .r3 100, .lsr .d .r12 .r12 16]) s fun t =>
      t.gpr .r11 = s.gpr .r9 ∧
      t.gpr .r12 = (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 100) 32).setWidth 64 >>> 16 ∧
      t.mem = s.mem ∧ Keep [.r11, .r12] s t := by
  refine WP.mono (WP.keep [.r11, .r12] (Q := fun t =>
      t.gpr .r11 = s.gpr .r9 ∧
      t.gpr .r12 = (s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 100) 32).setWidth 64 >>> 16 ∧
      t.mem = s.mem) ?_ (by decide) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  unfold mov
  irun [hk, BitVec.or_self]

theorem output_ok (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x s)
    (hk : KeyOk z s) :
    WP isa (.block output) s fun t =>
      OutHolds (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) x) t ∧
      t.mem = s.mem ∧ Keep roundWrites s t := by
  simp only [output, List.append_assoc]
  have k48 := hk.low 48 (by decide)
  simp only [Nat.reduceMul] at k48
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok .r6 96 (by decide) s hk.mask k48.1) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [hx.r6, setWidth_setWidth16, k48.2] at v₁
  have hk₁ := hk.keep e₁ m₁ (by decide) (by decide)
  have k₁ := hk₁.low 50 (by decide)
  simp only [Nat.reduceMul] at k₁
  rw [WP.block_append_iff]
  refine WP.mono (out1_ok s₁ k₁.1) fun s₂ ⟨a₂, d₂, m₂, e₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mul_keep s₂ ((e₂.gpr (by decide)).trans hk₁.mask)) fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  have e₁₃ : Keep [.r11, .r12] s₁ s₃ := (e₂.trans e₃).mono (by decide)
  have hm₃ : s₃.mem = s₁.mem := m₃.trans m₂
  have hk₃ := hk₁.keep e₁₃ hm₃ (by decide) (by decide)
  rw [WP.block_append_iff]
  have h4 : WP isa (.block [mov .r9 .r12]) s₃ fun t => t.gpr .r9 = s₃.gpr .r12 ∧ t.mem = s₃.mem ∧
      Keep [.r9] s₃ t := by
    refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = s₃.gpr .r12 ∧ t.mem = s₃.mem) ?_
      (by decide) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
    unfold mov
    irun [BitVec.or_self]
  refine WP.mono h4 fun s₄ ⟨v₄, m₄, e₄⟩ => ?_
  have hk₄ := hk₃.keep e₄ m₄ (by decide) (by decide)
  have k49 := hk₄.low 49 (by decide)
  simp only [Nat.reduceMul] at k49
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok (r := .r8) (by decide) 98 (by decide) s₄ (x.getD 2 0)
    ((e₄.gpr (by decide)).trans ((e₁₃.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.r8)))
    hk₄.mask k49.1) fun s₅ ⟨v₅, m₅, e₅⟩ => ?_
  have hk₅ := hk₄.keep e₅ m₅ (by decide) (by decide)
  have k50 := hk₅.low 50 (by decide)
  simp only [Nat.reduceMul] at k50
  refine WP.mono (addKey_ok (r := .r7) (by decide) 100 (by decide) s₅ (x.getD 1 0)
    ((e₅.gpr (by decide)).trans ((e₄.gpr (by decide)).trans ((e₁₃.gpr (by decide)).trans
      ((e₁.gpr (by decide)).trans hx.r7)))) hk₅.mask k50.1) fun s₆ ⟨v₆, m₆, e₆⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by rw [m₆, m₅, m₄, hm₃, m₁], ((((e₁.trans e₁₃).trans e₄).trans e₅).trans e₆).mono (by decide)⟩
  · rw [e₆.gpr (by decide), e₅.gpr (by decide), e₄.gpr (by decide), e₁₃.gpr (by decide), v₁,
      output_getD0]
  · rw [e₆.gpr (by decide), v₅, k49.2, output_getD1]
  · rw [v₆, k50.2, output_getD2]
  · rw [e₆.gpr (by decide), e₅.gpr (by decide), v₄, v₃, a₂, d₂, e₁.gpr (by decide), hx.r9,
      setWidth_setWidth16, hi16, hk₁.last, output_getD3]

/-! ## Storing -/

theorem storeWord_ok (r : Reg) (k : Nat) (hk : k < 4) (s : State) {a : Addr}
    (ha : s.gpr .r4 = a)
    (h1 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k + 1)) 1)
    (h0 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k)) 1) :
    WP isa (.block (storeWord r k)) s fun t =>
      t.mem = (s.mem.write (a + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r).setWidth 8)).write
        (a + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r >>> 8).setWidth 8) ∧
      Keep [.r11] s t := by
  refine WP.mono (WP.keep (c := .block (storeWord r k)) [.r11] (Q := fun t =>
      t.mem = (s.mem.write (a + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r).setWidth 8)).write
        (a + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r >>> 8).setWidth 8)) ?_
      (by simp [writesOnly, Code.allInstrs_eq, instrs, storeWord, dstOf]) rfl)
    fun t ⟨h, hk⟩ => ⟨h, hk⟩
  unfold storeWord
  irun [ha, h0, h1, show 2 * k < 2 ^ 15 by omega,
    show 2 * k + 1 < 2 ^ 15 by omega]

/-- The bytes of the block at `a` can be written. -/
def BlockWrite (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions s.wr (a + BitVec.ofNat 64 i) 1

theorem frame_write1 {a : Addr} {m m' : Mem} {j : Nat} (v : BitVec 8) (hj : j < 8)
    (h : Frame [⟨a, 8⟩] m m') : Frame [⟨a, 8⟩] m (m'.write (a + BitVec.ofNat 64 j) 1 v) :=
  h.write (List.mem_singleton_self _) (n := 1) v (Offset.contains_base a (by omega) (by omega))

theorem store_ok (y : Spec.Idea.State) (s : State) {a : Addr} (ha : s.gpr .r4 = a)
    (hw : BlockWrite s a) (hy : OutHolds y s) :
    WP isa (.block store) s fun t =>
      Spec.Idea.blockAt t.mem a = Spec.Idea.encodeBlock y ∧
      Frame [⟨a, 8⟩] s.mem t.mem ∧ Keep [.r11] s t := by
  simp only [store, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .r6 0 (by decide) s ha (hw _ (by decide))
    (hw _ (by decide))) fun s₁ ⟨m₁, e₁⟩ => ?_
  have ha₁ : s₁.gpr .r4 = a := (e₁.gpr (by decide)).trans ha
  have hw₁ : BlockWrite s₁ a := fun i hi => e₁.2.2 ▸ hw i hi
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .r8 1 (by decide) s₁ ha₁ (hw₁ _ (by decide))
    (hw₁ _ (by decide))) fun s₂ ⟨m₂, e₂⟩ => ?_
  have ha₂ : s₂.gpr .r4 = a := (e₂.gpr (by decide)).trans ha₁
  have hw₂ : BlockWrite s₂ a := fun i hi => e₂.2.2 ▸ hw₁ i hi
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .r7 2 (by decide) s₂ ha₂ (hw₂ _ (by decide))
    (hw₂ _ (by decide))) fun s₃ ⟨m₃, e₃⟩ => ?_
  have ha₃ : s₃.gpr .r4 = a := (e₃.gpr (by decide)).trans ha₂
  have hw₃ : BlockWrite s₃ a := fun i hi => e₃.2.2 ▸ hw₂ i hi
  refine WP.mono (storeWord_ok .r9 3 (by decide) s₃ ha₃ (hw₃ _ (by decide))
    (hw₃ _ (by decide))) fun s₄ ⟨m₄, e₄⟩ => ?_
  have v8 : s₁.gpr .r8 = (y.getD 1 0).setWidth 64 := (e₁.gpr (by decide)).trans hy.r8
  have v7 : s₂.gpr .r7 = (y.getD 2 0).setWidth 64 :=
    (e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hy.r7)
  have v9 : s₃.gpr .r9 = (y.getD 3 0).setWidth 64 :=
    (e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hy.r9))
  rw [v9] at m₄
  rw [v7] at m₃
  rw [v8] at m₂
  rw [hy.r6] at m₁
  rw [m₃, m₂, m₁] at m₄
  refine ⟨?_, ?_, (((e₁.trans e₂).trans e₃).trans e₄).mono (by decide)⟩
  · apply Vector.ext
    intro i hi
    simp only [Spec.Idea.blockAt, Vector.getElem_ofFn, m₄, encodeBlock_get _ hi]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
        i = 5 ∨ i = 6 ∨ i = 7 := by omega
    all_goals simp (disch := decide) only [write1_apply, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte, lo8, hi8, BitVec.ushiftRight_zero]
  · rw [m₄]
    repeat' apply frame_write1 _ (by decide)
    exact Frame.refl _ _

/-! ## A block -/

theorem cryptBlock_ok (z : Spec.Idea.Schedule) (s : State) {a : Addr} (ha : s.gpr .r4 = a)
    (hb : BlockRead s a) (hw : BlockWrite s a) (hk : KeyOk z s) :
    WP isa (.block cryptBlock) s fun t =>
      Spec.Idea.blockAt t.mem a = Spec.Idea.cryptBlock z (Spec.Idea.blockAt s.mem a) ∧
      Frame [⟨a, 8⟩] s.mem t.mem ∧ Keep roundWrites s t := by
  simp only [cryptBlock, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (load_ok s ha hb) fun s₁ ⟨x₁, m₁, e₁⟩ => ?_
  have k₁ := hk.keep e₁ m₁ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rounds_ok z _ 8 (by decide) s₁ x₁ k₁) fun s₂ ⟨x₂, m₂, e₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (output_ok z _ s₂ x₂ (k₁.keep e₂ m₂ (by decide) (by decide))) fun s₃ ⟨x₃, m₃, e₃⟩ => ?_
  have e₁₃ : Keep roundWrites s s₃ := ((e₁.trans e₂).trans e₃).mono (by decide)
  have m₁₃ : s₃.mem = s.mem := m₃.trans (m₂.trans m₁)
  refine WP.mono (store_ok _ s₃ ((e₁₃.gpr (by decide)).trans ha)
    (fun i hi => e₁₃.2.2 ▸ hw i hi) x₃) fun s₄ ⟨b₄, f₄, e₄⟩ => ?_
  refine ⟨?_, ?_, (e₁₃.trans e₄).mono (by decide)⟩
  · rw [b₄, Spec.Idea.cryptBlock, crypt_eq]
  · rw [← m₁₃]; exact f₄

end VG.Proof.Idea.PPC64LE
