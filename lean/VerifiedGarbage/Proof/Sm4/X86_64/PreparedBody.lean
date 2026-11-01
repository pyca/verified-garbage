module

public import VerifiedGarbage.Proof.Sm4.X86_64.Ecb
import VerifiedGarbage.Proof.Sm4.X86_64.Crypt16
import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.Impl.Sm4.X86_64.Prepared
import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
public import VerifiedGarbage.Proof.Sm4.Prepared

/-!
# SM4's batches under prepared round keys on x86-64: the code

What `vg_sm4_crypt_prepared` reads (`layout`, `Proof.Sm4.Prepared.Holds`) is
the masks and the table that ECB's rounds read (`ReadyAt`), word for word
(`WordsAt`, `holds_of_words`, `readyAt_of_words` and back): each of the
table's words is the plane of its round key (`planeOf`, the only words
related to it by `WordRel`, `wordRel_eq`).

`cryptBody_wp` runs the function's body, with its working space exactly
ECB's scratch buffer: the working space to `sb`, the callee-saved
registers to their slots, the sixteen blocks (`crypt16_wp`), and the
registers back.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Proof.Sm4 (WordRel specDir)

/-- The masks' slots and the table's, as byte ranges. -/
def layout : Prepared.Layout where
  table := [(8 * evenSlot, 24), (8 * tableSlot, 8 * (tableEnd - tableSlot))]
  encode k d i := (preparedWord k (ofSpecDir d) (i / 8)).extractLsb' (8 * (i % 8)) 8
  buf := 8 * tailSlot
  blocks := 16
  prepScratch := [(0, 8 * slots)]
  cryptScratch := [(0, 8 * evenSlot), (8 * (grpSlot + 1), 8 * (tableSlot - grpSlot - 1)),
    (8 * savedSlot, 8 * (slots - savedSlot))]
  size := 8 * slots

/-! ## The encoding -/

/-- The only planes of the word `x` are `planeOf x`. -/
theorem wordRel_eq {Q : Nat → BitVec 64} {x : Spec.Sm4.Word} (h : WordRel Q fun _ => x) {j : Nat} (hj : j < 8) :
    Q j = Impl.Sm4.planeOf x j := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [Proof.Sm4.planeOf_bit x j hp]
  have := h (p % 16) (by omega_arith) (p / 16) (by omega_arith) j hj
  rw [show 16 * (p / 16) + p % 16 = p by omega_arith] at this
  exact this

theorem keyEntry_eq (k : Spec.Sm4.Schedule) (d : Dir) (e : Nat) : keyEntry k d e = dirKeys d k e := by
  cases d <;> rfl

theorem ofSpecDir_specDir (d : Dir) : ofSpecDir (specDir d) = d := by cases d <;> rfl

theorem specDir_ofSpecDir (d : Spec.Sm4.Direction) : specDir (ofSpecDir d) = d := by cases d <;> rfl

/-- The masks and the table of round keys in the order of `d`: what ECB's
rounds read. -/
def ReadyAt (d : Dir) (m : Mem) (B : Addr) (k : Spec.Sm4.Schedule) : Prop :=
  MasksAt m B ∧ ∀ e < 32, WordRel (entryW m B e) fun _ => dirKeys d k e

/-- The words of the masks and the table, in the working space at `B`. -/
def WordsAt (m : Mem) (B : Addr) (k : Spec.Sm4.Schedule) (d : Dir) : Prop :=
  ∀ w, (evenSlot ≤ w ∧ w ≤ grpSlot) ∨ (tableSlot ≤ w ∧ w < tableEnd) →
    m.readW (wordAddr B w) 64 = preparedWord k d w

/-- Byte `j` of a word. -/
theorem byte_of_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    m (a + BitVec.ofNat 64 j) = (m.readW a 64).extractLsb' (8 * j) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

theorem word_byte_addr (B : Addr) (o : Nat) : B + BitVec.ofNat 64 o = wordAddr B (o / 8) + BitVec.ofNat 64 (o % 8) := by
  rw [wordAddr, VG.Offset.add_add]
  congr 2; omega_arith

theorem layout_table : layout.table = [(384, 24), (1024, 2048)] := rfl
theorem evenSlot_eq : evenSlot = 48 := rfl
theorem grpSlot_eq : grpSlot = 50 := rfl

theorem table_ranges (o : Nat) :
    (∃ r ∈ layout.table, ∃ i < r.2, o = r.1 + i) ↔
      (evenSlot ≤ o / 8 ∧ o / 8 ≤ grpSlot) ∨ (tableSlot ≤ o / 8 ∧ o / 8 < tableEnd) := by
  rw [layout_table, evenSlot_eq, grpSlot_eq, tableSlot_eq, tableEnd_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨r, hr | hr, i, hi, rfl⟩ <;> subst hr <;> dsimp only at hi ⊢ <;> omega_arith
  · intro h
    rcases h with h | h
    · exact ⟨_, .inl rfl, o - 384, by dsimp only; omega_arith, by dsimp only; omega_arith⟩
    · exact ⟨_, .inr rfl, o - 1024, by dsimp only; omega_arith, by dsimp only; omega_arith⟩

theorem holds_of_words {m : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : WordsAt m B k (ofSpecDir d)) : Proof.Sm4.Prepared.Holds layout m B k d := by
  intro r hr i hi
  have hw := (table_ranges (r.1 + i)).1 ⟨r, hr, i, hi, rfl⟩
  rw [word_byte_addr, byte_of_readW m _ (by omega_arith), h _ hw]
  rfl

theorem words_of_holds {m : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : Proof.Sm4.Prepared.Holds layout m B k d) : WordsAt m B k (ofSpecDir d) := by
  intro w hw
  simp only [Mem.readW, BitVec.setWidth_eq]
  refine Mem.read_eq_of_bytes fun j hj => ?_
  obtain ⟨r, hr, i, hi, ho⟩ := (table_ranges (8 * w + j)).2 (by
    rw [show (8 * w + j) / 8 = w by omega_arith]; exact hw)
  have := h r hr i hi
  rw [← ho, word_byte_addr, show (8 * w + j) / 8 = w by omega_arith, show (8 * w + j) % 8 = j by omega_arith] at this
  rw [this]
  show (preparedWord k (ofSpecDir d) ((8 * w + j) / 8)).extractLsb' (8 * ((8 * w + j) % 8)) 8 = _
  rw [show (8 * w + j) / 8 = w by omega_arith, show (8 * w + j) % 8 = j by omega_arith]

theorem entryW_eq (m : Mem) (B : Addr) (e j : Nat) :
    entryW m B e j = m.readW (wordAddr B (tableSlot + 8 * e + j)) 64 := by
  rw [entryW, wordAddr, show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]

theorem preparedWord_entry (k : Spec.Sm4.Schedule) (d : Dir) {e j : Nat} (hj : j < 8) :
    preparedWord k d (tableSlot + 8 * e + j) = Impl.Sm4.planeOf (dirKeys d k e) j := by
  have hc : ¬ (tableSlot + 8 * e + j < tableSlot) := by omega_arith
  simp only [preparedWord, hc, ↓reduceIte, keyEntry_eq]
  rw [show (tableSlot + 8 * e + j - tableSlot) / 8 = e by omega_arith, show (tableSlot + 8 * e + j - tableSlot) % 8 = j by omega_arith]

theorem preparedWord_mask (k : Spec.Sm4.Schedule) (d : Dir) {kv : Nat × BitVec 64} (hkv : kv ∈ keyMasks) :
    preparedWord k d kv.1 = kv.2 := by
  simp only [keyMasks, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl | rfl <;> rfl

theorem mask_in {kv : Nat × BitVec 64} (hkv : kv ∈ keyMasks) : evenSlot ≤ kv.1 ∧ kv.1 ≤ grpSlot := by
  simp only [keyMasks, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl | rfl <;> decide

theorem readyAt_of_words {m : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {d : Dir} (h : WordsAt m B k d) :
    ReadyAt d m B k := by
  refine ⟨fun kv hkv => by rw [h _ (.inl (mask_in hkv)), preparedWord_mask k d hkv], fun e he => ?_⟩
  refine (Proof.Sm4.planeOf_rel (dirKeys d k e)).congr fun j hj => ?_
  rw [entryW_eq, h _ (.inr (by rw [tableSlot_eq, tableEnd_eq]; omega_arith)), preparedWord_entry k d hj]

theorem words_of_readyAt {m : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {d : Dir} (h : ReadyAt d m B k) :
    WordsAt m B k d := by
  intro w hw
  rcases hw with hw | hw
  · have hkv : ∃ kv ∈ keyMasks, kv.1 = w := by
      rw [evenSlot_eq, grpSlot_eq] at hw
      simp only [keyMasks, List.mem_cons, List.not_mem_nil, or_false]
      rcases (by omega_arith : w = 48 ∨ w = 49 ∨ w = 50) with rfl | rfl | rfl
      · exact ⟨_, .inl rfl, rfl⟩
      · exact ⟨_, .inr (.inl rfl), rfl⟩
      · exact ⟨_, .inr (.inr rfl), rfl⟩
    obtain ⟨kv, hkv, rfl⟩ := hkv
    rw [h.1 kv hkv, preparedWord_mask k d hkv]
  · obtain ⟨e, j, hj, rfl⟩ : ∃ e j, j < 8 ∧ w = tableSlot + 8 * e + j :=
      ⟨(w - tableSlot) / 8, (w - tableSlot) % 8, by omega_arith, by omega_arith⟩
    have he : e < 32 := by rw [tableSlot_eq, tableEnd_eq] at hw; omega_arith
    rw [← entryW_eq, preparedWord_entry k d hj]
    exact wordRel_eq (h.2 e he) hj

/-! ## The body -/

/-- The rounds with the round keys in the order of `d` are its cipher. -/
theorem quads_spec (d : Dir) (sch : Spec.Sm4.Schedule) (blk : Spec.Sm4.Block) :
    Proof.Sm4.outBlock (Proof.Sm4.quads .enc (dirKeys d sch) 8 (Proof.Sm4.ofBlock blk)) =
      Proof.Sm4.blockFn sch (specDir d) blk := by
  cases d
  · simp only [Proof.Sm4.blockFn, specDir, Spec.Sm4.encryptBlock, Proof.Sm4.crypt_eq]; rfl
  · simp only [Proof.Sm4.blockFn, specDir, Spec.Sm4.decryptBlock, Proof.Sm4.crypt_eq]; rfl

theorem saveRegs_eq : saveRegs = (List.range 6).map fun i => st (savedSlot + i) (sreg i) := rfl

theorem restoreRegs_eq : restoreRegs = (List.range 6).map fun i => movS (sreg i) (savedSlot + i) := rfl

/-- The registers' saves write their slots alone. -/
theorem save_saved {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨wordAddr b savedSlot, 48⟩] s.mem s'.mem := by
  obtain ⟨s', e', v', f', g', rd', wr'⟩ := Proof.Modes.X86_64.stores_ok savedSlot sreg 6 s hb
    (fun i hi => ⟨_, hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [savedSlot_eq, slots_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)⟩)
    (by rw [savedSlot_eq]; omega_arith)
  exact ⟨s', by rw [saveRegs_eq]; exact e', v', g', rd', wr', f'⟩

/-- The registers' restores read their slots. -/
theorem restore_loads {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 6, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 6, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e', v', o', m', rd', wr'⟩ := Proof.Modes.X86_64.loads_ok savedSlot sreg 6 s hb
    (fun i _ => (sreg_ne i).1) (by decide)
    (fun i hi => ⟨_, List.mem_append_right _ hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [savedSlot_eq, slots_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)⟩)
  exact ⟨s', by rw [restoreRegs_eq]; exact e', fun i hi => by rw [v' i hi, hs i hi], o', m', rd', wr'⟩

/-- `vg_sm4_crypt_prepared`'s body, with its working space at `rdi` ECB's
scratch buffer, holding the round keys `k` in the order of `d`. -/
theorem cryptBody_wp {s₀ : State} (hwr : (⟨s₀.gpr .rdi, 8 * slots⟩ : Region) ∈ s₀.wr)
    (fitB : (s₀.gpr .rdi).toNat + 8 * slots ≤ 2 ^ 64) {k : Spec.Sm4.Schedule} {d : Dir}
    (hr : ReadyAt d s₀.mem (s₀.gpr .rdi) k) :
    WP isa cryptPrepared s₀ fun s' => (∀ i < 6, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      s'.gpr .rsp = s₀.gpr .rsp ∧ s'.gpr sb = s₀.gpr .rdi ∧ ReadyAt d s'.mem (s₀.gpr .rdi) k ∧
      Frame [⟨s₀.gpr .rdi, 8 * tableSlot⟩, ⟨wordAddr (s₀.gpr .rdi) savedSlot, 48⟩] s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      ∀ j < 16, Spec.Sm4.blockAt s'.mem (s₀.gpr .rdi + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        Proof.Sm4.blockFn k (specDir d) (Spec.Sm4.blockAt s₀.mem (s₀.gpr .rdi + BitVec.ofNat 64 (8 * tailSlot + 16 * j))) := by
  generalize hb : s₀.gpr .rdi = b at hwr fitB hr ⊢
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .rdi
  have b₁ : s₁.gpr sb = b := r₁.trans hb
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_saved (b := b) (by rw [wr₁]; exact hwr) b₁
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := slotAddr_ok s₂ .rdi tableEnd (by decide)
  have b₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), g₂, b₁]
  have hfit := fitB
  rw [slots_eq] at hfit
  have slot₃ : ∀ w < savedSlot, s₃.mem.readW (wordAddr b w) 64 = s₀.mem.readW (wordAddr b w) 64 := fun w hw => by
    rw [m₃, ← m₁]
    refine f₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint b (.inl (by rw [savedSlot_eq] at hw ⊢; omega_arith)) (by rw [savedSlot_eq] at hw; omega_arith)
      (by rw [savedSlot_eq]; omega_arith)
  have hkey : KeyCtx s₃ (dirKeys d k) :=
    { scr := by rw [b₃, wr₃, wr₂, wr₁]; exact hwr
      fit := by rw [b₃]; exact fitB
      keys := fun e he => (hr.2 e he).congr fun j hj => by
        rw [b₃, entryW_eq, entryW_eq, slot₃ (tableSlot + 8 * e + j) (by rw [tableSlot_eq, savedSlot_eq]; omega_arith)] }
  have hm₃ : MasksOk s₃ := fun kv hkv => by
    show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
    rw [b₃, slot₃ _ (by have := mask_in hkv; rw [grpSlot_eq] at this; rw [savedSlot_eq]; omega_arith)]
    exact hr.1 kv hkv
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃], ?_⟩)
  refine WP.seq (WP.mono (crypt16_wp hkey hm₃ (by rw [r₃, b₃, g₂, b₁])) fun s₄ ⟨c₄, o₄⟩ => ?_)
  have base₄ : s₄.gpr sb = b := by rw [c₄.base, b₃]
  have f₄ : Frame [⟨b, 8 * tableSlot⟩] s₃.mem s₄.mem := by have := c₄.frame; rw [b₃] at this; exact this
  have sv₄ : Saved s₁ b s₄.mem := fun i hi => by
    rw [← sv₂ i hi, ← m₃]
    refine f₄.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableSlot_eq, savedSlot_eq]; omega_arith)
      (by rw [savedSlot_eq]; omega_arith)
  obtain ⟨s₅, e₅, rg₅, og₅, m₅, rd₅, wr₅⟩ := restore_loads (by rw [c₄.wr, wr₃, wr₂, wr₁]; exact hwr) base₄ sv₄
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [og₅ _ (fun i _ => by unfold sreg; split <;> decide), c₄.keep _ (by decide) (by decide),
      o₃ _ (by decide), g₂, o₁ _ (by decide)]
  refine WP.of_runBlock ⟨s₅, e₅, fun i hi => by rw [rg₅ i hi, o₁ _ (sreg_ne i).1], rsp₅,
    (og₅ sb (fun i _ => (sreg_ne i).1.symm)).trans base₄, ?_, ?_,
    by rw [rd₅, c₄.rd, rd₃, rd₂, rd₁], by rw [wr₅, c₄.wr, wr₃, wr₂, wr₁], fun j hj => ?_⟩
  · refine ⟨fun kv hkv => by rw [m₅]; exact c₄.masks.at base₄ kv hkv, fun e he => (hr.2 e he).congr fun j hj => ?_⟩
    rw [entryW_eq, entryW_eq, m₅, ← slot₃ (tableSlot + 8 * e + j) (by rw [tableSlot_eq, savedSlot_eq]; omega_arith)]
    refine f₄.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (by rw [tableSlot_eq]; omega_arith) (by rw [tableSlot_eq]; omega_arith)
  · rw [m₅]
    have l₂ : Frame [⟨b, 8 * tableSlot⟩, ⟨wordAddr b savedSlot, 48⟩] s₀.mem s₃.mem := by
      rw [m₃, ← m₁]
      exact f₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
    exact l₂.trans (f₄.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  · have := o₄ j hj
    simp only [tailBlock, base₄, b₃] at this
    rw [m₅, this, quads_spec, m₃]
    refine congrArg _ (Vector.ext fun i hi => ?_)
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [VG.Offset.add_add, ← m₁]
    refine f₂.bytes (R := ⟨b, 8 * savedSlot⟩) (fun r hr => ?_) (by show 8 * savedSlot ≤ 2 ^ 64; rw [savedSlot_eq]; omega_arith)
      (by show 8 * tailSlot + 16 * j + i < 8 * savedSlot; rw [tailSlot_eq, savedSlot_eq]; omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.base_disjoint b (by omega_arith) (by rw [savedSlot_eq]; omega_arith)

end VG.Proof.Sm4.X86_64
