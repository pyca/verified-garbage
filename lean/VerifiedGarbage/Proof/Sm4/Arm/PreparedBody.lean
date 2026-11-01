module

public import VerifiedGarbage.Proof.Sm4.Arm.Ecb
public import VerifiedGarbage.Impl.Sm4.Arm.Prepared
import VerifiedGarbage.Proof.Sm4.Arm.Crypt8
import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
public import VerifiedGarbage.Proof.Sm4.Prepared
public import VerifiedGarbage.Proof.Sm4.Contract

/-! # SM4 prepared round keys and batches on ARMv7: functional correctness -/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (sb movR)
open VG.Proof.Sm4 (specDirArm)

/-- The table's slots, as bytes. -/
def layout : Prepared.Layout where
  table := [(4 * tableSlot, 4 * (tableEnd - tableSlot))]
  encode k d i := (preparedWord k (ofSpecDir d) (i / 4)).extractLsb' (8 * (i % 4)) 8
  buf := 4 * tailSlot
  blocks := 8
  prepScratch := [(0, 4 * slots)]
  cryptScratch := [(0, 4 * tableSlot), (4 * savedSlot, 4 * (slots - savedSlot))]
  size := 4 * slots

/-! ## The encoding -/

/-- The table of round keys in the order of `d`: what ECB's rounds read. -/
def ReadyAt (d : Dir) (m : Mem) (B : BitVec 32) (k : Spec.Sm4.Schedule) : Prop :=
  ∀ e < 32, W32.WordRel (entryW m B e) fun _ => dirKeys d k e

/-- The only planes of the word `x` are `planeOf32 x`. -/
theorem wordRel_eq {Q : Nat → BitVec 32} {x : Spec.Sm4.Word} (h : W32.WordRel Q fun _ => x) {j : Nat} (hj : j < 8) :
    Q j = Impl.Sm4.planeOf32 x j := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [Proof.Sm4.planeOf32_bit x j hp]
  have := h (p % 8) (by omega) (p / 8) (by omega) j hj
  rw [show 8 * (p / 8) + p % 8 = p by omega] at this
  exact this

theorem keyEntry_eq (k : Spec.Sm4.Schedule) (d : Dir) (e : Nat) : keyEntry k d e = dirKeys d k e := by
  cases d <;> rfl

theorem ofSpecDir_specDirArm (d : Dir) : ofSpecDir (specDirArm d) = d := by cases d <;> rfl
theorem specDirArm_ofSpecDir (d : Spec.Sm4.Direction) : specDirArm (ofSpecDir d) = d := by cases d <;> rfl

/-- The words `vg_sm4_prepare_keys` writes, in the working space at `B`. -/
def WordsAt (m : Mem) (B : BitVec 32) (k : Spec.Sm4.Schedule) (d : Dir) : Prop :=
  ∀ w, tableSlot ≤ w → w < tableEnd → m.readW (wordAddr B w) 32 = preparedWord k d w

theorem layout_table : layout.table = [(384, 1024)] := rfl

/-- Byte `j` of the word of slot `w`. -/
theorem table_byte {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) {o : Nat} (ho : o < 4 * tableEnd) :
    B.setWidth 64 + BitVec.ofNat 64 o = wordAddr B (o / 4) + BitVec.ofNat 64 (o % 4) := by
  rw [wordAddr, addr_add (by rw [slots_eq] at hfit; rw [tableEnd_eq] at ho; omega), VG.Offset.add_add]
  congr 2; omega

theorem holds_of_words {m : Mem} {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) {k : Spec.Sm4.Schedule}
    {d : Spec.Sm4.Direction} (h : WordsAt m B k (ofSpecDir d)) : Proof.Sm4.Prepared.Holds layout m (B.setWidth 64) k d := by
  intro r hr i hi
  rw [layout_table, List.mem_singleton] at hr
  subst hr
  dsimp only at hi ⊢
  rw [table_byte hfit (by rw [tableEnd_eq]; omega), Mem.readW_byte m _ (by omega),
    h _ (by rw [tableSlot_eq]; omega) (by rw [tableEnd_eq]; omega)]
  rfl

theorem words_of_holds {m : Mem} {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) {k : Spec.Sm4.Schedule}
    {d : Spec.Sm4.Direction} (h : Proof.Sm4.Prepared.Holds layout m (B.setWidth 64) k d) :
    WordsAt m B k (ofSpecDir d) := by
  intro w h1 h2
  simp only [Mem.readW]
  refine (congrArg (BitVec.setWidth 32) (Mem.read_eq_of_bytes (n := 4) (v := preparedWord k (ofSpecDir d) w)
    fun j hj => ?_)).trans (BitVec.setWidth_eq _)
  rw [tableSlot_eq] at h1; rw [tableEnd_eq] at h2
  have := h (384, 1024) (by rw [layout_table]; exact List.mem_singleton_self _) (4 * w + j - 384) (by omega)
  dsimp only at this
  rw [show 384 + (4 * w + j - 384) = 4 * w + j by omega, table_byte hfit (by rw [tableEnd_eq]; omega),
    show (4 * w + j) / 4 = w by omega, show (4 * w + j) % 4 = j by omega] at this
  rw [this]
  show (preparedWord k (ofSpecDir d) ((4 * w + j) / 4)).extractLsb' (8 * ((4 * w + j) % 4)) 8 = _
  rw [show (4 * w + j) / 4 = w by omega, show (4 * w + j) % 4 = j by omega]

theorem preparedWord_entry (k : Spec.Sm4.Schedule) (d : Dir) {e j : Nat} (hj : j < 8) :
    preparedWord k d (tableSlot + 8 * e + j) = Impl.Sm4.planeOf32 (dirKeys d k e) j := by
  rw [preparedWord, keyEntry_eq, show (tableSlot + 8 * e + j - tableSlot) / 8 = e by omega,
    show (tableSlot + 8 * e + j - tableSlot) % 8 = j by omega]

theorem readyAt_of_words {m : Mem} {B : BitVec 32} {k : Spec.Sm4.Schedule} {d : Dir} (h : WordsAt m B k d) :
    ReadyAt d m B k := fun e he =>
  (Proof.Sm4.planeOf32_rel (dirKeys d k e)).congr fun j hj => by
    rw [entryW, h _ (by omega) (by rw [tableEnd_eq, tableSlot_eq] at *; omega), preparedWord_entry k d hj]

theorem words_of_readyAt {m : Mem} {B : BitVec 32} {k : Spec.Sm4.Schedule} {d : Dir} (h : ReadyAt d m B k) :
    WordsAt m B k d := by
  intro w h1 h2
  obtain ⟨e, j, hj, rfl⟩ : ∃ e j, j < 8 ∧ w = tableSlot + 8 * e + j :=
    ⟨(w - tableSlot) / 8, (w - tableSlot) % 8, by omega, by omega⟩
  have he : e < 32 := by rw [tableSlot_eq, tableEnd_eq] at *; omega
  rw [← entryW, preparedWord_entry k d hj]
  exact wordRel_eq (h e he) hj

theorem ofSpecDir_directionOf (decrypt : BitVec 32) :
    ofSpecDir (Proof.Sm4.directionOf decrypt.toNat) = dirOf decrypt := by
  unfold dirOf Proof.Sm4.directionOf
  by_cases h : decrypt = 0
  · subst h; rfl
  · have h' : decrypt.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    simp only [h, h', ite_false]; rfl

/-- Preparing a table saves the registers, runs ECB's key setup once, and
restores the registers. -/
theorem prepareBody_wp {s₀ : State} {b sched : BitVec 32} (hw : ScrIn s₀.wr b)
    (hb : s₀.gpr .r2 = b) (hsc : s₀.gpr .r0 = sched)
    (hK : (⟨State.addr sched, 128⟩ : Region) ∈ s₀.rd ++ s₀.wr)
    (fitK : sched.toNat + 128 ≤ 2 ^ 32)
    (dKS : Region.Disjoint ⟨State.addr sched, 128⟩ ⟨State.addr b, 4 * slots⟩) :
    WP isa prepareKeys s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s'.mem ∧
      WordsAt s'.mem b (Spec.Sm4.scheduleAt s₀.mem (State.addr sched)) (dirOf (s₀.gpr .r1)) := by
  obtain ⟨s₁, e₁, b₁, k₁, g₁, sv₁, f₁, rd₁, wr₁, sp₁⟩ := prologue_ok hb hw
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ .r3 .r1
  have b₂ : s₂.gpr sb = b := by rw [o₂ _ (by decide), b₁]
  have k₂ : s₂.gpr .r12 = sched := by rw [o₂ _ (by decide), k₁, hsc]
  have d₂ : s₂.gpr .r3 = s₀.gpr .r1 := by rw [r₂, g₁ _ (by decide) (by decide)]
  have hk₂ : SchedPre s₂ b sched :=
    ⟨b₂, by rw [wr₂, wr₁]; exact hw.mem, hw.fit,
      by rw [rd₂, wr₂, rd₁, wr₁]; exact hK, fitK, dKS⟩
  have f₂ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₂.mem := by rw [m₂]; exact f₁
  have sch₂ := hk₂.sched_eq (Nat.le_refl _) f₂
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, ?_⟩)
  · rw [show saveRegs .r2 ++ [movR sb .r2, movR .r12 .r0, movR .r3 .r1] =
      (saveRegs .r2 ++ [movR sb .r2, movR .r12 .r0]) ++ [movR .r3 .r1] from rfl,
      runBlock_app, e₁, Option.bind_some, e₂]
  refine WP.seq (WP.mono (keysAny_wp hk₂ k₂ d₂) fun s₃ h₃ => ?_)
  have sv₃ : Saved s₀ b s₃.mem := fun i hi => by
    rw [← sv₁ i hi, ← m₂]
    refine h₃.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [slot_addr (by have := hw.fit; rw [savedSlot_eq, slots_eq] at *; omega)]
    exact VG.Offset.disjoint_base _ (by rw [savedSlot_eq, tableEnd_eq]; omega)
      (by rw [savedSlot_eq]; omega)
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r12 sb
  obtain ⟨s₅, e₅, rg₅, -, m₅, rd₅, wr₅, sp₅⟩ := restore_ok
    (by rw [wr₄, h₃.wr, wr₂, wr₁]; exact hw) (by rw [r₄, h₃.pre.base]) (by rw [m₄]; exact sv₃)
  refine WP.of_runBlock ⟨s₅, ?_, rg₅, by rw [rd₅, rd₄, h₃.rd, rd₂, rd₁],
    by rw [wr₅, wr₄, h₃.wr, wr₂, wr₁], by rw [sp₅, sp₄, h₃.sp, sp₂, sp₁], ?_, ?_⟩
  · rw [runBlock_app, e₄, Option.bind_some, e₅]
  · rw [m₅, m₄]
    exact f₂.trans (h₃.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega)⟩)
  · rw [m₅, m₄, ← sch₂]
    apply words_of_readyAt
    intro e he
    have h := h₃.key.keys e he
    rw [h₃.pre.base] at h
    exact h

/-- The rounds with keys in the selected order implement that direction. -/
theorem prepared_quads_spec (d : Dir) (sch : Spec.Sm4.Schedule) (blk : Spec.Sm4.Block) :
    Proof.Sm4.outBlock (Proof.Sm4.quads .enc (dirKeys d sch) 8 (Proof.Sm4.ofBlock blk)) =
      Proof.Sm4.blockFn sch (specDirArm d) blk := by
  cases d
  · simp only [Proof.Sm4.blockFn, specDirArm, Spec.Sm4.encryptBlock, Proof.Sm4.crypt_eq]; rfl
  · simp only [Proof.Sm4.blockFn, specDirArm, Spec.Sm4.decryptBlock, Proof.Sm4.crypt_eq]; rfl

/-- A byte of a slot below the table's end. -/
theorem prepared_byte {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {o : Nat} (ho : o < 4 * tableEnd) (m : Mem) :
    m (State.addr b + BitVec.ofNat 64 o) =
      (m.readW (wordAddr b (o / 4)) 32).extractLsb' (8 * (o % 4)) 8 := by
  change m (b.setWidth 64 + BitVec.ofNat 64 o) = _
  rw [table_byte hfit ho, Mem.readW_byte m _ (by omega)]

/-- The cipher transforms the eight buffered blocks, preserving its key table. -/
theorem cryptBody_wp {s₀ : State} {b : BitVec 32} (hw : ScrIn s₀.wr b)
    (hb : s₀.gpr .r0 = b) {k : Spec.Sm4.Schedule} {d : Dir} (hr : ReadyAt d s₀.mem b k) :
    WP isa cryptPrepared s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s'.mem ∧ ReadyAt d s'.mem b k ∧
      ∀ j < 8, Spec.Sm4.blockAt s'.mem (State.addr b + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) =
        Proof.Sm4.blockFn k (specDirArm d)
          (Spec.Sm4.blockAt s₀.mem (State.addr b + BitVec.ofNat 64 (4 * tailSlot + 16 * j))) := by
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁, o₁⟩ := save_ok hw hb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ sb .r0
  have b₂ : s₂.gpr sb = b := by rw [r₂, g₁, hb]
  have slot₂ : ∀ w < savedSlot, s₂.mem.readW (wordAddr b w) 32 = s₀.mem.readW (wordAddr b w) 32 :=
    fun w hw => by rw [m₂]; exact o₁ w hw
  have key₂ : KeyCtx s₂ (dirKeys d k) :=
    ⟨by rw [b₂, wr₂, wr₁]; exact hw.mem, by rw [b₂]; exact hw.fit,
      fun e he => (hr e he).congr fun j hj => by
        rw [b₂, entryW, entryW, slot₂ _ (by rw [tableSlot_eq, savedSlot_eq]; omega)]⟩
  have tail₂ : ∀ j < 8, tailBlock s₂ j =
      Spec.Sm4.blockAt s₀.mem (State.addr b + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) := by
    intro j hj
    apply Vector.ext; intro i hi
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn, b₂]
    rw [VG.Offset.add_add, prepared_byte hw.fit (o := 4 * tailSlot + 16 * j + i) (by rw [tailSlot_eq, tableEnd_eq]; omega) s₂.mem,
      prepared_byte hw.fit (o := 4 * tailSlot + 16 * j + i) (by rw [tailSlot_eq, tableEnd_eq]; omega) s₀.mem,
      slot₂ _ (by rw [tailSlot_eq, savedSlot_eq]; omega)]
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, ?_⟩)
  · rw [runBlock_app, e₁, Option.bind_some, e₂]
  refine WP.seq (WP.mono (crypt8_wp key₂) fun s₃ ⟨c₃, out₃⟩ => ?_)
  have b₃ : s₃.gpr sb = b := c₃.base.trans b₂
  have f₃ : Frame [⟨State.addr b, 4 * tableSlot⟩] s₂.mem s₃.mem := by rw [← b₂]; exact c₃.frame
  have sv₃ : Saved s₀ b s₃.mem := fun i hi => by
    rw [← sv₁ i hi, ← m₂]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [slot_addr (by have := hw.fit; rw [savedSlot_eq, slots_eq] at *; omega)]
    exact VG.Offset.disjoint_base _ (by rw [savedSlot_eq, tableSlot_eq]; omega)
      (by rw [savedSlot_eq]; omega)
  obtain ⟨s₄, e₄, r₄, -, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r12 sb
  obtain ⟨s₅, e₅, rg₅, -, m₅, rd₅, wr₅, sp₅⟩ := restore_ok
    (by rw [wr₄, c₃.wr, wr₂, wr₁]; exact hw) (by rw [r₄, b₃]) (by rw [m₄]; exact sv₃)
  refine WP.of_runBlock ⟨s₅, ?_, rg₅, by rw [rd₅, rd₄, c₃.rd, rd₂, rd₁],
    by rw [wr₅, wr₄, c₃.wr, wr₂, wr₁], by rw [sp₅, sp₄, c₃.sp, sp₂, sp₁], ?_, ?_, ?_⟩
  · rw [runBlock_app, e₄, Option.bind_some, e₅]
  · rw [m₅, m₄]
    have f₂ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₂.mem := by rw [m₂]; exact f₁
    exact f₂.trans (f₃.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega)⟩)
  · intro e he
    refine (hr e he).congr fun j hj => ?_
    rw [entryW, entryW, m₅, m₄, ← slot₂ (tableSlot + 8 * e + j) (by rw [tableSlot_eq, savedSlot_eq]; omega)]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [slot_addr (by have := hw.fit; rw [tableSlot_eq, slots_eq] at *; omega)]
    exact VG.Offset.disjoint_base _ (by omega) (by rw [tableSlot_eq]; omega)
  · intro j hj
    have h := out₃ j hj
    simp only [tailBlock, b₃] at h
    rw [m₅, m₄, h, prepared_quads_spec]
    exact congrArg _ (tail₂ j hj)

end VG.Proof.Sm4.Arm
