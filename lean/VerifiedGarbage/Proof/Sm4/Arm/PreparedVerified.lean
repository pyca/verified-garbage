module

public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import Init.Data.BitVec.Basic
meta import Init.Data.BitVec.Basic
public import Init.Data.Vector.Basic
meta import Init.Data.Vector.Basic
public import VerifiedGarbage.TCB.Arm.Isa
meta import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Impl.Sm4.Arm.Prepared
meta import VerifiedGarbage.Impl.Sm4.Arm.Prepared
public import VerifiedGarbage.Proof.Sm4.Arm.Group
meta import VerifiedGarbage.Proof.Sm4.Arm.Group
public import VerifiedGarbage.Proof.Sm4.Common
meta import VerifiedGarbage.Proof.Sm4.Common
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Prepared
meta import VerifiedGarbage.Proof.Sm4.Prepared
public import VerifiedGarbage.Proof.Sm4.Arm.Ecb
import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
meta import VerifiedGarbage.Proof.Sm4.Arm.Ecb
meta import VerifiedGarbage.Proof.Sm4.Planes
meta import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
meta import VerifiedGarbage.Proof.Sm4.Contract

/-! ### `Sm4.Arm.PreparedBody`, which this module and modules that import it used -/

section

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
  have := h (p % 8) (by omega_using []) (p / 8) (by omega_using [hp]) j hj
  rw [show 8 * (p / 8) + p % 8 = p by omega_using []] at this
  exact this

theorem keyEntry_eq (k : Spec.Sm4.Schedule) (d : Dir) (e : Nat) : keyEntry k d e = dirKeys d k e := by
  cases d <;> rfl

theorem specDirArm_ofSpecDir (d : Spec.Sm4.Direction) : specDirArm (ofSpecDir d) = d := by cases d <;> rfl

/-- The words `vg_sm4_prepare_keys` writes, in the working space at `B`. -/
def WordsAt (m : Mem) (B : BitVec 32) (k : Spec.Sm4.Schedule) (d : Dir) : Prop :=
  ∀ w, tableSlot ≤ w → w < tableEnd → m.readW (wordAddr B w) 32 = preparedWord k d w

theorem layout_table : layout.table = [(384, 1024)] := rfl

/-- Byte `j` of the word of slot `w`. -/
theorem table_byte {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) {o : Nat} (ho : o < 4 * tableEnd) :
    B.setWidth 64 + BitVec.ofNat 64 o = wordAddr B (o / 4) + BitVec.ofNat 64 (o % 4) := by
  rw [wordAddr, addr_add (by rw [slots_eq] at hfit; rw [tableEnd_eq] at ho; omega_using [hfit, ho]), VG.Offset.add_add]
  congr 2; omega_using []

theorem holds_of_words {m : Mem} {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) {k : Spec.Sm4.Schedule}
    {d : Spec.Sm4.Direction} (h : WordsAt m B k (ofSpecDir d)) : Proof.Sm4.Prepared.Holds layout m (B.setWidth 64) k d := by
  intro r hr i hi
  rw [layout_table, List.mem_singleton] at hr
  subst hr
  dsimp only at hi ⊢
  rw [table_byte hfit (by rw [tableEnd_eq]; omega_using [hi]), Mem.readW_byte m _ (by omega_using []),
    h _ (by rw [tableSlot_eq]; omega_using []) (by rw [tableEnd_eq]; omega_using [hi])]
  rfl

theorem words_of_holds {m : Mem} {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) {k : Spec.Sm4.Schedule}
    {d : Spec.Sm4.Direction} (h : Proof.Sm4.Prepared.Holds layout m (B.setWidth 64) k d) :
    WordsAt m B k (ofSpecDir d) := by
  intro w h1 h2
  simp only [Mem.readW]
  refine (congrArg (BitVec.setWidth 32) (Mem.read_eq_of_bytes (n := 4) (v := preparedWord k (ofSpecDir d) w)
    fun j hj => ?_)).trans (BitVec.setWidth_eq _)
  rw [tableSlot_eq] at h1; rw [tableEnd_eq] at h2
  have := h (384, 1024) (by rw [layout_table]; exact List.mem_singleton_self _) (4 * w + j - 384) (by omega_using [h2, hj])
  dsimp only at this
  rw [show 384 + (4 * w + j - 384) = 4 * w + j by omega_using [h1], table_byte hfit (by rw [tableEnd_eq]; omega_using [h2, hj]),
    show (4 * w + j) / 4 = w by omega_using [hj], show (4 * w + j) % 4 = j by omega_using [hj]] at this
  rw [this]
  show (preparedWord k (ofSpecDir d) ((4 * w + j) / 4)).extractLsb' (8 * ((4 * w + j) % 4)) 8 = _
  rw [show (4 * w + j) / 4 = w by omega_using [hj], show (4 * w + j) % 4 = j by omega_using [hj]]

theorem preparedWord_entry (k : Spec.Sm4.Schedule) (d : Dir) {e j : Nat} (hj : j < 8) :
    preparedWord k d (tableSlot + 8 * e + j) = Impl.Sm4.planeOf32 (dirKeys d k e) j := by
  rw [preparedWord, keyEntry_eq, show (tableSlot + 8 * e + j - tableSlot) / 8 = e by omega_using [hj],
    show (tableSlot + 8 * e + j - tableSlot) % 8 = j by omega_using [hj]]

theorem readyAt_of_words {m : Mem} {B : BitVec 32} {k : Spec.Sm4.Schedule} {d : Dir} (h : WordsAt m B k d) :
    ReadyAt d m B k := fun e he =>
  (Proof.Sm4.planeOf32_rel (dirKeys d k e)).congr fun j hj => by
    rw [entryW, h _ (by omega_using []) (by rw [tableEnd_eq, tableSlot_eq] at *; omega_using [he, hj]), preparedWord_entry k d hj]

theorem words_of_readyAt {m : Mem} {B : BitVec 32} {k : Spec.Sm4.Schedule} {d : Dir} (h : ReadyAt d m B k) :
    WordsAt m B k d := by
  intro w h1 h2
  obtain ⟨e, j, hj, rfl⟩ : ∃ e j, j < 8 ∧ w = tableSlot + 8 * e + j :=
    ⟨(w - tableSlot) / 8, (w - tableSlot) % 8, by omega_using [], by omega_using [h1]⟩
  have he : e < 32 := by rw [tableSlot_eq, tableEnd_eq] at *; omega_using [h2]
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
    rw [slot_addr (by have := hw.fit; rw [savedSlot_eq, slots_eq] at *; omega_using [hi, this])]
    exact VG.Offset.disjoint_base _ (by rw [savedSlot_eq, tableEnd_eq]; omega_using [])
      (by rw [savedSlot_eq]; omega_using [hi])
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r12 sb
  obtain ⟨s₅, e₅, rg₅, -, m₅, rd₅, wr₅, sp₅⟩ := restore_ok
    (by rw [wr₄, h₃.wr, wr₂, wr₁]; exact hw) (by rw [r₄, h₃.pre.base]) (by rw [m₄]; exact sv₃)
  refine WP.of_runBlock ⟨s₅, ?_, rg₅, by rw [rd₅, rd₄, h₃.rd, rd₂, rd₁],
    by rw [wr₅, wr₄, h₃.wr, wr₂, wr₁], by rw [sp₅, sp₄, h₃.sp, sp₂, sp₁], ?_, ?_⟩
  · rw [runBlock_app, e₄, Option.bind_some, e₅]
  · rw [m₅, m₄]
    exact f₂.trans (h₃.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega_using [])⟩)
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
  rw [table_byte hfit ho, Mem.readW_byte m _ (by omega_using [])]

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
        rw [b₂, entryW, entryW, slot₂ _ (by rw [tableSlot_eq, savedSlot_eq]; omega_using [he, hj])]⟩
  have tail₂ : ∀ j < 8, tailBlock s₂ j =
      Spec.Sm4.blockAt s₀.mem (State.addr b + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) := by
    intro j hj
    apply Vector.ext; intro i hi
    simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn, b₂]
    rw [VG.Offset.add_add, prepared_byte hw.fit (o := 4 * tailSlot + 16 * j + i) (by rw [tailSlot_eq, tableEnd_eq]; omega_using [hj, hi]) s₂.mem,
      prepared_byte hw.fit (o := 4 * tailSlot + 16 * j + i) (by rw [tailSlot_eq, tableEnd_eq]; omega_using [hj, hi]) s₀.mem,
      slot₂ _ (by rw [tailSlot_eq, savedSlot_eq]; omega_using [hj, hi])]
  refine WP.seq (WP.of_runBlock ⟨s₂, ?_, ?_⟩)
  · rw [runBlock_app, e₁, Option.bind_some, e₂]
  refine WP.seq (WP.mono (crypt8_wp key₂) fun s₃ ⟨c₃, out₃⟩ => ?_)
  have b₃ : s₃.gpr sb = b := c₃.base.trans b₂
  have f₃ : Frame [⟨State.addr b, 4 * tableSlot⟩] s₂.mem s₃.mem := by rw [← b₂]; exact c₃.frame
  have sv₃ : Saved s₀ b s₃.mem := fun i hi => by
    rw [← sv₁ i hi, ← m₂]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [slot_addr (by have := hw.fit; rw [savedSlot_eq, slots_eq] at *; omega_using [hi, this])]
    exact VG.Offset.disjoint_base _ (by rw [savedSlot_eq, tableSlot_eq]; omega_using [])
      (by rw [savedSlot_eq]; omega_using [hi])
  obtain ⟨s₄, e₄, r₄, -, m₄, rd₄, wr₄, sp₄⟩ := movR_ok s₃ .r12 sb
  obtain ⟨s₅, e₅, rg₅, -, m₅, rd₅, wr₅, sp₅⟩ := restore_ok
    (by rw [wr₄, c₃.wr, wr₂, wr₁]; exact hw) (by rw [r₄, b₃]) (by rw [m₄]; exact sv₃)
  refine WP.of_runBlock ⟨s₅, ?_, rg₅, by rw [rd₅, rd₄, c₃.rd, rd₂, rd₁],
    by rw [wr₅, wr₄, c₃.wr, wr₂, wr₁], by rw [sp₅, sp₄, c₃.sp, sp₂, sp₁], ?_, ?_, ?_⟩
  · rw [runBlock_app, e₄, Option.bind_some, e₅]
  · rw [m₅, m₄]
    have f₂ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₂.mem := by rw [m₂]; exact f₁
    exact f₂.trans (f₃.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_using [])⟩)
  · intro e he
    refine (hr e he).congr fun j hj => ?_
    rw [entryW, entryW, m₅, m₄, ← slot₂ (tableSlot + 8 * e + j) (by rw [tableSlot_eq, savedSlot_eq]; omega_using [he, hj])]
    refine f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [slot_addr (by have := hw.fit; rw [tableSlot_eq, slots_eq] at *; omega_using [he, hj, this])]
    exact VG.Offset.disjoint_base _ (by omega_using []) (by rw [tableSlot_eq]; omega_using [he, hj])
  · intro j hj
    have h := out₃ j hj
    simp only [tailBlock, b₃] at h
    rw [m₅, m₄, h, prepared_quads_spec]
    exact congrArg _ (tail₂ j hj)

end VG.Proof.Sm4.Arm

end

end

/-! # SM4 prepared-key helpers on ARMv7 meet their contracts -/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4 (specDirArm)
open VG.Proof.Sm4.Prepared (Holds Keeps)

theorem prepared_size_eq : layout.size = 4 * slots := rfl

/-- Restrict the working space to the portion the helper uses. -/
abbrev prepNarrow (s : State) (b : BitVec 32) : State := s.withRegions s.rd [⟨State.addr b, 4 * slots⟩]

theorem prep_widen {c : Prog isa} {s s' : State} {b : BitVec 32} {len : Nat} {t : List Leak}
    (hw : s.wr = [⟨State.addr b, len⟩]) (hl : 4 * slots ≤ len)
    (he : Exec isa c (prepNarrow s b) t s') : Exec isa c s t (s'.withRegions s.rd s.wr) := by
  have hc : Covers [⟨State.addr b, 4 * slots⟩] s.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr b, len⟩, by rw [hw]; simp, 0, by rw [BitVec.add_zero], by change 0 + 4 * slots ≤ len; omega_using [hl]⟩
  have h := Exec.widen he (Covers.append (Covers.refl _) hc) hc
  change Exec isa c s t (s'.withRegions s.rd s.wr) at h
  exact h

theorem prepared_abi {s s' : State} (h : ∀ i < 9, s'.gpr (sreg i) = s.gpr (sreg i))
    (hsp : s'.sp = s.sp) : abiPreserved s s' := by
  refine ⟨fun r hr => ?_, hsp⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h 0 (by omega_using [])
  · exact h 1 (by omega_using [])
  · exact h 2 (by omega_using [])
  · exact h 3 (by omega_using [])
  · exact h 4 (by omega_using [])
  · exact h 5 (by omega_using [])
  · exact h 6 (by omega_using [])
  · exact h 7 (by omega_using [])
  · exact h 8 (by omega_using [])

theorem prepared_keeps_outside {m m' : Mem} {b : BitVec 32} {len : Nat}
    (hf : Frame [⟨State.addr b, 4 * slots⟩] m m') (fit : b.toNat + len * 8 ≤ 2 ^ 32)
    {i : Nat} (hi : i < len * 8) (hout : 4 * slots ≤ i) :
    m' (State.addr b + BitVec.ofNat 64 i) = m (State.addr b + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Region.Contains] at hc
  rw [Mem.sub_ofNat_toNat _ (by omega_using [fit, hi])] at hc
  omega_using [hout, hc]

def prepArm : Contract isa where
  pre s :=
    s.rd = [⟨State.addr (s.gpr .r0), 128⟩] ∧
    s.wr = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat * 8⟩] ∧
    Region.Disjoint ⟨State.addr (s.gpr .r0), 128⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat * 8⟩ ∧
    (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat * 8 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ≤ 1 ∧ layout.size ≤ 8 * (s.gpr .r3).toNat
  post s s' :=
    Holds layout s'.mem (State.addr (s.gpr .r2)) (Spec.Sm4.scheduleAt s.mem (State.addr (s.gpr .r0)))
      (Proof.Sm4.directionOf (s.gpr .r1).toNat) ∧
    Keeps (State.addr (s.gpr .r2)) (s.gpr .r3).toNat layout.prepScratch s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

theorem prepared_prep_correct (s : State) (hs : prepArm.pre s) :
    ∃ t s', Exec isa prepareKeys s t s' ∧ abiPreserved s s' ∧ prepArm.post s s' := by
  obtain ⟨rd, wr, sep, fitK, fitW, -, hsz⟩ := hs
  rw [prepared_size_eq] at hsz
  have hl : 4 * slots ≤ (s.gpr .r3).toNat * 8 := by omega_using [hsz]
  have hw : ScrIn (prepNarrow s (s.gpr .r2)).wr (s.gpr .r2) := ⟨by simp, by omega_using [fitW, hsz]⟩
  obtain ⟨t, s', he, hg, -, -, hsp, hf, hwords⟩ := prepareBody_wp hw rfl rfl
    (by simp [prepNarrow, rd]) fitK (sep.sub_right (Region.sub_prefix hl))
  have he' := prep_widen wr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', prepared_abi hg hsp, ?_, fun i hi hout => ?_⟩
  · apply holds_of_words hw.fit
    rw [ofSpecDir_directionOf]
    exact hwords
  · apply prepared_keeps_outside hf fitW (by omega_using [hi])
    have h := hout (0, 4 * slots) (by simp [layout])
    dsimp only at h
    omega_using [h]

def cryptArm : Contract isa where
  pre s :=
    s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩] ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧ layout.size ≤ 8 * (s.gpr .r1).toNat ∧
    ∃ k d, Holds layout s.mem (State.addr (s.gpr .r0)) k d
  post s s' :=
    (∀ k d, Holds layout s.mem (State.addr (s.gpr .r0)) k d →
      Spec.Sm4.blocksAt s'.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Sm4.ecb k d (Spec.Sm4.blocksAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
    Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

theorem prepared_blocks_of (B : Addr) {m m' : Mem} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : ∀ j < 8, Spec.Sm4.blockAt m' (B + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) =
      Proof.Sm4.blockFn k d (Spec.Sm4.blockAt m (B + BitVec.ofNat 64 (4 * tailSlot + 16 * j)))) :
    Spec.Sm4.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Sm4.ecb k d (Spec.Sm4.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Sm4.ecb_eq]
  simp only [Spec.Sm4.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hj
  simp only [Function.comp_apply, VG.Offset.add_add]
  exact h j hj

theorem prepared_crypt_correct (s : State) (hs : cryptArm.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptArm.post s s' := by
  obtain ⟨-, wr, fitW, hsz, k₀, d₀, hH⟩ := hs
  rw [prepared_size_eq] at hsz
  have hl : 4 * slots ≤ (s.gpr .r1).toNat * 8 := by omega_using [hsz]
  have hw : ScrIn (prepNarrow s (s.gpr .r0)).wr (s.gpr .r0) := ⟨by simp, by omega_using [fitW, hsz]⟩
  have hwords := words_of_holds hw.fit hH
  obtain ⟨t, s', he, hg, -, -, hsp, hf, hR, -⟩ :=
    cryptBody_wp hw rfl (readyAt_of_words hwords)
  have he' := prep_widen wr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', prepared_abi hg hsp, fun k d h => ?_, fun i hi hout => ?_⟩
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, -, hb₂⟩ :=
      cryptBody_wp hw rfl (readyAt_of_words (words_of_holds hw.fit h))
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    apply prepared_blocks_of
    intro j hj
    have hb := hb₂ j hj
    rw [specDirArm_ofSpecDir] at hb
    exact hb
  · by_cases hi' : i < 4 * slots
    · have hLo := hout (0, 4 * tableSlot) (by simp [layout])
      have hHi := hout (4 * savedSlot, 4 * (slots - savedSlot)) (by simp [layout])
      dsimp only at hLo hHi
      have htable : 384 ≤ i ∧ i < 1408 := by
        rw [slots_eq] at hi'
        rw [tableSlot_eq] at hLo; rw [savedSlot_eq, slots_eq] at hHi
        omega_using [hi', hLo, hHi]
      have hH' := holds_of_words hw.fit (words_of_readyAt hR)
      have a := hH (384, 1024) (by rw [layout_table]; simp) (i - 384) (by omega_using [htable])
      have a' := hH' (384, 1024) (by rw [layout_table]; simp) (i - 384) (by omega_using [htable])
      dsimp only at a a'
      rw [show 384 + (i - 384) = i by omega_using [htable]] at a a'
      exact a'.trans a.symm
    · exact prepared_keeps_outside hf fitW (by omega_using [hi]) (by omega_using [hi'])

end VG.Proof.Sm4.Arm
