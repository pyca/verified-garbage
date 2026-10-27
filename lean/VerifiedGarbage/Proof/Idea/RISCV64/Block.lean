module

public import VerifiedGarbage.Proof.Idea.RISCV64.Round
public import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Idea.Memory
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.MRun
meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun

/-!
# IDEA on RISC-V: a block

`cryptBlock_ok`: `Impl.Idea.RISCV64.cryptBlock` replaces the block at `a1`
with `Spec.Idea.cryptBlock` of it under the subkeys at `a0`: the block's
words are loaded a byte at a time (`load_ok`), run through the rounds
(`rounds_ok`) and the output transformation (`output_ok`), and stored a
byte at a time (`store_ok`).
-/

@[expose] public section

namespace VG.Proof.Idea.RISCV64

open VG VG.RISCV64 VG.Impl.Idea.RISCV64

/-! ## Loading -/

theorem loadWord_ok {r : Reg} (hr : r ≠ .t3 ∧ r ≠ .a1) (k : Nat) (hk : k < 4) (s : State) {a : Addr}
    (ha : s.gpr .a1 = a)
    (h0 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k)) 1)
    (h1 : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 (2 * k + 1)) 1) :
    WP isa (.block (loadWord r k)) s fun t =>
      t.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++ s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      t.mem = s.mem ∧ Keep [.t3, r] s t := by
  refine WP.mono (WP.keep (c := .block (loadWord r k)) [.t3, r] (Q := fun t =>
      t.gpr r = (s.mem (a + BitVec.ofNat 64 (2 * k)) ++
        s.mem (a + BitVec.ofNat 64 (2 * k + 1))).setWidth 64 ∧
      t.mem = s.mem) ?_ (by simp [writesOnly, Code.allInstrs_eq, instrs, loadWord, dstOf]) rfl)
    fun t ⟨⟨h₁, h₂⟩, hk⟩ => ⟨h₁, h₂, hk⟩
  unfold loadWord
  mrun [ha, h0, h1, hr.1, Ne.symm hr.1, hr.2, Ne.symm hr.2, show 2 * k < 2048 by omega, show 2 * k + 1 < 2048 by omega]
  exact bytes16 _ _

/-- The bytes of the block at `a` can be read. -/
def BlockRead (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 i) 1

theorem BlockRead.keep {rs : List Reg} {s s' : State} {a : Addr} (h : BlockRead s a)
    (hk : Keep rs s s') : BlockRead s' a := by
  intro i hi; rw [hk.2.1, hk.2.2]; exact h i hi

theorem load_ok (s : State) {a : Addr} (ha : s.gpr .a1 = a) (hb : BlockRead s a) :
    WP isa (.block load) s fun t =>
      Holds (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem a)) t ∧ t.mem = s.mem ∧
      Keep [.t3, .a3, .a4, .a5, .a6] s t := by
  have w (k : Nat) (hk : k < 4) := decodeBlock_blockAt s.mem a hk
  simp only [load, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .a3) (by decide) 0 (by decide) s ha (hb _ (by decide))
    (hb _ (by decide))) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .a4) (by decide) 1 (by decide) s₁ ((e₁.gpr (by decide)).trans ha)
    ((hb.keep e₁) _ (by decide)) ((hb.keep e₁) _ (by decide))) fun s₂ ⟨v₂, m₂, e₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadWord_ok (r := .a5) (by decide) 2 (by decide) s₂
    ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans ha))
    ((hb.keep e₁ |>.keep e₂) _ (by decide)) ((hb.keep e₁ |>.keep e₂) _ (by decide)))
    fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  refine WP.mono (loadWord_ok (r := .a6) (by decide) 3 (by decide) s₃
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

/-- The output words: `Y₁` in `a3`, `Y₂` in `a5`, `Y₃` in `a4`, `Y₄` in `a6`. -/
structure OutHolds (y : Spec.Idea.State) (s : State) : Prop where
  a3 : s.gpr .a3 = (y.getD 0 0).setWidth 64
  a5 : s.gpr .a5 = (y.getD 1 0).setWidth 64
  a4 : s.gpr .a4 = (y.getD 2 0).setWidth 64
  a6 : s.gpr .a6 = (y.getD 3 0).setWidth 64

theorem output_ok (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x s)
    (hk : KeyOk z s) :
    WP isa (.block output) s fun t =>
      OutHolds (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) x) t ∧
      t.mem = s.mem ∧ Keep roundWrites s t := by
  simp only [output, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok hk (r := .a3) (by decide) (k := 48) (by decide)) fun s₁ ⟨v₁, m₁, e₁⟩ => ?_
  rw [hx.a3, setWidth_setWidth16] at v₁
  have hk₁ := hk.keep e₁ m₁ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulKey_ok hk₁ (r := .a6) (by decide) (k := 51) (by decide)) fun s₂ ⟨v₂, m₂, e₂⟩ => ?_
  rw [e₁.gpr (by decide), hx.a6, setWidth_setWidth16] at v₂
  have hk₂ := hk₁.keep e₂ m₂ (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addKey_ok hk₂ (r := .a5) (by decide) (k := 49) (by decide) (x.getD 2 0)
    ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.a5))) fun s₃ ⟨v₃, m₃, e₃⟩ => ?_
  have hk₃ := hk₂.keep e₃ m₃ (by decide) (by decide)
  refine WP.mono (addKey_ok hk₃ (r := .a4) (by decide) (k := 50) (by decide) (x.getD 1 0)
    ((e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hx.a4))))
    fun s₄ ⟨v₄, m₄, e₄⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by rw [m₄, m₃, m₂, m₁],
    (((e₁.trans e₂).trans e₃).trans e₄).mono (by decide)⟩
  · rw [e₄.gpr (by decide), e₃.gpr (by decide), e₂.gpr (by decide), v₁, output_getD0]
  · rw [e₄.gpr (by decide), v₃, output_getD1]
  · rw [v₄, output_getD2]
  · rw [e₄.gpr (by decide), e₃.gpr (by decide), v₂, output_getD3]

/-! ## Storing -/

theorem storeWord_ok (r : Reg) (k : Nat) (hk : k < 4) (s : State) {a : Addr}
    (ha : s.gpr .a1 = a)
    (h1 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k + 1)) 1)
    (h0 : InRegions s.wr (a + BitVec.ofNat 64 (2 * k)) 1) :
    WP isa (.block (storeWord r k)) s fun t =>
      t.mem = (s.mem.write (a + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r).setWidth 8)).write
        (a + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r >>> 8).setWidth 8) ∧
      Keep [.t3] s t := by
  refine WP.mono (WP.keep (c := .block (storeWord r k)) [.t3] (Q := fun t =>
      t.mem = (s.mem.write (a + BitVec.ofNat 64 (2 * k + 1)) 1 ((s.gpr r).setWidth 8)).write
        (a + BitVec.ofNat 64 (2 * k)) 1 ((s.gpr r >>> 8).setWidth 8)) ?_
      (by rfl) rfl)
    fun t ⟨h, hk⟩ => ⟨h, hk⟩
  unfold storeWord
  mrun [ha, h0, h1, show 2 * k < 2048 by omega,
    show 2 * k + 1 < 2048 by omega]

/-- The bytes of the block at `a` can be written. -/
def BlockWrite (s : State) (a : Addr) : Prop :=
  ∀ i < 8, InRegions s.wr (a + BitVec.ofNat 64 i) 1

theorem frame_write1 {a : Addr} {m m' : Mem} {j : Nat} (v : BitVec 8) (hj : j < 8)
    (h : Frame [⟨a, 8⟩] m m') : Frame [⟨a, 8⟩] m (m'.write (a + BitVec.ofNat 64 j) 1 v) :=
  h.write (List.mem_singleton_self _) (n := 1) v (Offset.contains_base a (by omega) (by omega))

theorem store_ok (y : Spec.Idea.State) (s : State) {a : Addr} (ha : s.gpr .a1 = a)
    (hw : BlockWrite s a) (hy : OutHolds y s) :
    WP isa (.block store) s fun t =>
      Spec.Idea.blockAt t.mem a = Spec.Idea.encodeBlock y ∧
      Frame [⟨a, 8⟩] s.mem t.mem ∧ Keep [.t3] s t := by
  simp only [store, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .a3 0 (by decide) s ha (hw _ (by decide))
    (hw _ (by decide))) fun s₁ ⟨m₁, e₁⟩ => ?_
  have ha₁ : s₁.gpr .a1 = a := (e₁.gpr (by decide)).trans ha
  have hw₁ : BlockWrite s₁ a := fun i hi => e₁.2.2 ▸ hw i hi
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .a5 1 (by decide) s₁ ha₁ (hw₁ _ (by decide))
    (hw₁ _ (by decide))) fun s₂ ⟨m₂, e₂⟩ => ?_
  have ha₂ : s₂.gpr .a1 = a := (e₂.gpr (by decide)).trans ha₁
  have hw₂ : BlockWrite s₂ a := fun i hi => e₂.2.2 ▸ hw₁ i hi
  rw [WP.block_append_iff]
  refine WP.mono (storeWord_ok .a4 2 (by decide) s₂ ha₂ (hw₂ _ (by decide))
    (hw₂ _ (by decide))) fun s₃ ⟨m₃, e₃⟩ => ?_
  have ha₃ : s₃.gpr .a1 = a := (e₃.gpr (by decide)).trans ha₂
  have hw₃ : BlockWrite s₃ a := fun i hi => e₃.2.2 ▸ hw₂ i hi
  refine WP.mono (storeWord_ok .a6 3 (by decide) s₃ ha₃ (hw₃ _ (by decide))
    (hw₃ _ (by decide))) fun s₄ ⟨m₄, e₄⟩ => ?_
  have v8 : s₁.gpr .a5 = (y.getD 1 0).setWidth 64 := (e₁.gpr (by decide)).trans hy.a5
  have v7 : s₂.gpr .a4 = (y.getD 2 0).setWidth 64 :=
    (e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hy.a4)
  have v9 : s₃.gpr .a6 = (y.getD 3 0).setWidth 64 :=
    (e₃.gpr (by decide)).trans ((e₂.gpr (by decide)).trans ((e₁.gpr (by decide)).trans hy.a6))
  rw [v9] at m₄
  rw [v7] at m₃
  rw [v8] at m₂
  rw [hy.a3] at m₁
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

theorem cryptBlock_ok (z : Spec.Idea.Schedule) (s : State) {a : Addr} (ha : s.gpr .a1 = a)
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

end VG.Proof.Idea.RISCV64
