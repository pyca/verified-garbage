module

public import VerifiedGarbage.Proof.Sm4.X86.Ecb
public import VerifiedGarbage.Impl.Sm4.X86.Prepared
import VerifiedGarbage.Proof.Sm4.Planes
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Sm4.X86.Crypt8
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.X86.LayersLit
public import VerifiedGarbage.Proof.Sm4.Prepared
public import VerifiedGarbage.Proof.Sm4.Contract

/-!
# SM4's prepared round keys and batches on x86 (32-bit): the code

What `vg_sm4_prepare_keys` writes (`layout`, `Proof.Sm4.Prepared.Holds`) is
the table that ECB's rounds read (`ReadyAt`), word for word (`WordsAt`,
`holds_of_words`, `words_of_holds`, `readyAt_of_words`,
`words_of_readyAt`): each of the table's words is the plane of its round
key (`planeOf32`, the only words related to it by `W32.WordRel`,
`wordRel_eq`).

`prepareBody_wp` and `cryptBody_wp` run the two functions' bodies: ECB's
prologue, the key setup (`keys_wp`) or the eight blocks (`crypt8_wp`), and
the epilogue.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb argOp)
open VG.Proof.Sm4 (specDirX86)

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

theorem ofSpecDir_specDirX86 (d : Dir) : ofSpecDir (specDirX86 d) = d := by cases d <;> rfl
theorem specDirX86_ofSpecDir (d : Spec.Sm4.Direction) : specDirX86 (ofSpecDir d) = d := by cases d <;> rfl

/-- The words `vg_sm4_prepare_keys` writes, in the working space at `B`. -/
def WordsAt (m : Mem) (B : BitVec 32) (k : Spec.Sm4.Schedule) (d : Dir) : Prop :=
  ∀ w, tableSlot ≤ w → w < tableEnd → m.readW (wordAddr B w) 32 = preparedWord k d w

theorem layout_table : layout.table = [(384, 1024)] := rfl

/-- Byte `j` of the word of slot `w`. -/
theorem table_byte {B : BitVec 32} (hfit : B.toNat + 4 * slots ≤ 2 ^ 32) {o : Nat} (ho : o < 4 * tableEnd) :
    B.setWidth 64 + BitVec.ofNat 64 o = wordAddr B (o / 4) + BitVec.ofNat 64 (o % 4) := by
  rw [wordAddr, addr_eq (by rw [slots_eq] at hfit; rw [tableEnd_eq] at ho; omega), VG.Offset.add_add]
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

/-! ## The bodies -/

/-- The direction `decrypt` selects. -/
def dirOf (decrypt : BitVec 32) : Dir := if decrypt = 0 then .encrypt else .decrypt

theorem ofSpecDir_dirOf (decrypt : BitVec 32) : ofSpecDir (Proof.Sm4.directionOf decrypt.toNat) = dirOf decrypt := by
  unfold dirOf Proof.Sm4.directionOf
  by_cases h : decrypt = 0
  · subst h; rfl
  · have h' : decrypt.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    simp only [h, h', ite_false]; rfl

/-- `vg_sm4_prepare_keys`'s body, from its arguments: the schedule, the
direction, and the working space at `b` (writable, `slots` slots or more). -/
theorem prepareBody_wp {s₀ : State} {b sched : BitVec 32} (hw : ScrIn s₀.wr b)
    (harg : ∀ i < 3, InRegions (s₀.rd ++ s₀.wr) (s₀.ea (argOp i)) 4)
    (hsc : s₀.mem.readW (s₀.ea (argOp 0)) 32 = sched) (hb : s₀.mem.readW (s₀.ea (argOp 2)) 32 = b)
    (hK : (⟨sched.setWidth 64, 128⟩ : Region) ∈ s₀.rd ++ s₀.wr) (fitK : sched.toNat + 128 ≤ 2 ^ 32)
    (dKS : Region.Disjoint ⟨sched.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * slots⟩)
    (dAS : ∀ i < 3, Region.Disjoint ⟨s₀.ea (argOp i), 4⟩ ⟨b.setWidth 64, 4 * slots⟩) :
    WP isa prepareKeys s₀ fun s' => (∀ i < 4, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ s'.gpr .esp = s₀.gpr .esp ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s'.mem ∧
      WordsAt s'.mem b (Spec.Sm4.scheduleAt s₀.mem (sched.setWidth 64))
        (dirOf (s₀.mem.readW (s₀.ea (argOp 1)) 32)) := by
  have hfit := hw.fit
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, rd₁, wr₁, f₁, -⟩ := save_ok (k := 2) hw (harg 2 (by decide)) hb
  have esp₁ : s₁.gpr .esp = s₀.gpr .esp := g₁ _ (by decide) (by decide)
  have ea₁ : ∀ i, s₁.ea (argOp i) = s₀.ea (argOp i) := fun i => by
    show (s₁.gpr .esp + _).setWidth 64 = (s₀.gpr .esp + _).setWidth 64; rw [esp₁]
  have argR : ∀ {m : Mem}, Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem m → ∀ i < 3,
      m.readW (s₀.ea (argOp i)) 32 = s₀.mem.readW (s₀.ea (argOp i)) 32 := fun hf i hi =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dAS i hi) (by decide)
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldArg_ok s₁ .eax 1 (by rw [rd₁, wr₁, ea₁]; exact harg 1 (by decide))
  let s₃ := arithFlags s₂ (s₂.gpr .eax &&& s₂.gpr .eax) false false
  have e₃ : runBlock isa (saveRegs 2 ++ [.mov .eax (.mem (argOp 1)), .alu .test .eax (.reg .eax)]) s₀ = some s₃ := by
    rw [show saveRegs 2 ++ [.mov .eax (.mem (argOp 1)), .alu .test .eax (.reg .eax)] =
      saveRegs 2 ++ ([.mov .eax (.mem (argOp 1))] ++ [.alu .test .eax (.reg .eax)]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some]
    rfl
  let dec := s₀.mem.readW (s₀.ea (argOp 1)) 32
  have eax₂ : s₂.gpr .eax = dec := by rw [v₂, ea₁, argR f₁ 1 (by decide)]
  have g₃ : ∀ r, r ≠ .eax → s₃.gpr r = s₁.gpr r := fun r hr => o₂ r hr
  have hk₃ : SchedPre s₃ b sched :=
    ⟨by rw [g₃ _ (by decide)]; exact b₁, by show ScrIn s₂.wr b; rw [wr₂, wr₁]; exact hw,
      by show _ ∈ s₂.rd ++ s₂.wr; rw [rd₂, wr₂, rd₁, wr₁]; exact hK, fitK, dKS⟩
  have f₀₃ : Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s₃.mem := by
    show Frame _ s₀.mem s₂.mem; rw [m₂]; exact f₁
  have hsch : Spec.Sm4.scheduleAt s₃.mem (sched.setWidth 64) = Spec.Sm4.scheduleAt s₀.mem (sched.setWidth 64) :=
    hk₃.sched_eq (Nat.le_refl _) f₀₃
  refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
  have ea₃ : ∀ i, s₃.ea (argOp i) = s₀.ea (argOp i) := fun i => by
    show (s₃.gpr .esp + _).setWidth 64 = (s₀.gpr .esp + _).setWidth 64; rw [g₃ _ (by decide), esp₁]
  have arg₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.ea (argOp 0)) 4 := by
    show InRegions (s₂.rd ++ s₂.wr) _ 4; rw [rd₂, wr₂, rd₁, wr₁, ea₃]; exact harg 0 (by decide)
  have sch₃ : s₃.mem.readW (s₃.ea (argOp 0)) 32 = sched := by
    rw [ea₃, show s₃.mem = s₁.mem from m₂, argR f₁ 0 (by decide), hsc]
  have hz₃ : s₃.zf = some (dec == 0) := by
    rw [RegUpd.zf_arithFlags, eax₂, BitVec.and_self]
  refine WP.seq (WP.mono (Q := KeysPost s₃ b sched (dirOf dec))
    (WP.ite (dec == 0) ((eval_e s₃).trans hz₃) (fun h => ?_) (fun h => ?_)) fun s₄ k₄ => ?_)
  · have : dirOf dec = .encrypt := by simp only [dirOf, beq_iff_eq.mp h, ite_true]
    rw [this]; exact keys_wp .encrypt hk₃ arg₃ sch₃
  · have h' : dec ≠ 0 := fun e => by rw [e] at h; exact absurd h (by decide)
    have : dirOf dec = .decrypt := by simp only [dirOf, h', ite_false]
    rw [this]; exact keys_wp .decrypt hk₃ arg₃ sch₃
  have base₄ : s₄.gpr sb = b := k₄.pre.base
  have sv₄ : Saved s₀ b s₄.mem := fun i hi => by
    rw [← sv₁ i hi, ← show s₃.mem = s₁.mem from m₂]
    exact slot_keep hfit (lo := tableEnd) (hi := slots) (Nat.le_refl _) k₄.frame
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by rw [tableEnd_eq, slots_eq]; decide))
      (by rw [savedSlot_eq, tableEnd_eq]; omega) (by rw [savedSlot_eq, slots_eq]; omega)
  obtain ⟨s₅, e₅, rg₅, o₅, m₅, rd₅, wr₅⟩ := restore_ok (s₀ := s₀) (b := b)
    (by rw [k₄.wr]; show ScrIn s₂.wr b; rw [wr₂, wr₁]; exact hw) base₄ sv₄
  have esp₄ : s₄.gpr .esp = s₀.gpr .esp := by
    rw [k₄.regs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g₃ _ (by decide), esp₁]
  refine WP.of_runBlock ⟨s₅, e₅, rg₅, by rw [o₅ _ (fun i hi => by revert i; decide), esp₄],
    by rw [rd₅, k₄.rd]; show s₂.rd = _; rw [rd₂, rd₁], by rw [wr₅, k₄.wr]; show s₂.wr = _; rw [wr₂, wr₁], ?_, ?_⟩
  · rw [m₅]
    refine f₁.trans ?_
    rw [← show s₃.mem = s₁.mem from m₂]
    exact k₄.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableEnd_eq, slots_eq]; omega)⟩
  · rw [m₅, ← hsch]
    refine words_of_readyAt fun e he => ?_
    have := k₄.key.keys e he
    rw [base₄] at this
    exact this

theorem quads_spec (d : Dir) (sch : Spec.Sm4.Schedule) (blk : Spec.Sm4.Block) :
    Proof.Sm4.outBlock (Proof.Sm4.quads .enc (dirKeys d sch) 8 (Proof.Sm4.ofBlock blk)) =
      Proof.Sm4.blockFn sch (specDirX86 d) blk := by
  cases d
  · simp only [Proof.Sm4.blockFn, specDirX86, Spec.Sm4.encryptBlock, Proof.Sm4.crypt_eq]; rfl
  · simp only [Proof.Sm4.blockFn, specDirX86, Spec.Sm4.decryptBlock, Proof.Sm4.crypt_eq]; rfl

/-- `vg_sm4_crypt_prepared`'s body, with its working space at `b` (the first
argument) holding the round keys `k` in the order of `d`. -/
theorem cryptBody_wp {s₀ : State} {b : BitVec 32} (hw : ScrIn s₀.wr b)
    (harg : InRegions (s₀.rd ++ s₀.wr) (s₀.ea (argOp 0)) 4) (hb : s₀.mem.readW (s₀.ea (argOp 0)) 32 = b)
    {k : Spec.Sm4.Schedule} {d : Dir} (hr : ReadyAt d s₀.mem b k) :
    WP isa cryptPrepared s₀ fun s' => (∀ i < 4, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ s'.gpr .esp = s₀.gpr .esp ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ Frame [⟨b.setWidth 64, 4 * slots⟩] s₀.mem s'.mem ∧
      (∀ w, tableSlot ≤ w → w < savedSlot → s'.mem.readW (wordAddr b w) 32 = s₀.mem.readW (wordAddr b w) 32) ∧
      ∀ j < 8, Spec.Sm4.blockAt s'.mem (b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j)) =
        Proof.Sm4.blockFn k (specDirX86 d) (Spec.Sm4.blockAt s₀.mem (b.setWidth 64 + BitVec.ofNat 64 (4 * tailSlot + 16 * j))) := by
  have hfit := hw.fit
  obtain ⟨s₁, e₁, b₁', g₁, sv₁, rd₁, wr₁, f₁, k₁⟩ := save_ok (k := 0) hw harg hb
  have b₁ : s₁.gpr sb = b := b₁'
  have hkey : KeyCtx s₁ (dirKeys d k) :=
    { scr := by rw [b₁, wr₁]; exact hw
      keys := fun e he => (hr e he).congr fun j hj => by
        rw [b₁]; exact k₁ _ (by rw [savedSlot_eq, tableSlot_eq]; omega) }
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (crypt8_wp hkey) fun s₂ ⟨c₂, o₂⟩ => ?_)
  have base₂ : s₂.gpr sb = b := by rw [c₂.base]; exact b₁
  have f₂ : Frame [⟨b.setWidth 64, 4 * tableSlot⟩] s₁.mem s₂.mem := by
    have := c₂.frame; rw [show s₁.gpr sb = b from b₁] at this; exact this
  have keep₂ : ∀ w, tableSlot ≤ w → w < slots → s₂.mem.readW (wordAddr b w) 32 = s₁.mem.readW (wordAddr b w) 32 :=
    fun w h1 h2 => slot_keep hfit (lo := tableSlot) (hi := slots) (Nat.le_refl _) f₂
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by rw [tableSlot_eq, slots_eq]; decide)) h1 h2
  have sv₂ : Saved s₀ b s₂.mem := fun i hi => by
    rw [← sv₁ i hi]; exact keep₂ _ (by rw [savedSlot_eq, tableSlot_eq]; omega) (by rw [savedSlot_eq, slots_eq]; omega)
  obtain ⟨s₃, e₃, rg₃, o₃, m₃, rd₃, wr₃⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [c₂.wr, wr₁]; exact hw) base₂ sv₂
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [c₂.keep _ (by decide) (by decide), g₁ _ (by decide) (by decide)]
  refine WP.of_runBlock ⟨s₃, e₃, rg₃, by rw [o₃ _ (fun i hi => by revert i; decide), esp₂],
    by rw [rd₃, c₂.rd, rd₁], by rw [wr₃, c₂.wr, wr₁], ?_, fun w h1 h2 => ?_, fun j hj => ?_⟩
  · rw [m₃]
    exact f₁.trans (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega)⟩)
  · rw [m₃, keep₂ w h1 (by rw [savedSlot_eq] at h2; rw [slots_eq]; omega), k₁ w h2]
  · have := o₂ j hj
    simp only [tailBlock, base₂] at this
    rw [m₃, this, quads_spec]
    refine congrArg _ (Vector.ext fun i hi => ?_)
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    have ho : 4 * tailSlot + 16 * j + i < 4 * tableEnd := by rw [tailSlot_eq, tableEnd_eq]; omega
    rw [b₁, VG.Offset.add_add, table_byte hfit ho, Mem.readW_byte s₁.mem _ (by omega), Mem.readW_byte s₀.mem _ (by omega),
      k₁ _ (by rw [tailSlot_eq, savedSlot_eq]; omega)]

end VG.Proof.Sm4.X86
