module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.Ecb
import VerifiedGarbage.Proof.Sm4.PPC64LE.Crypt16
public import VerifiedGarbage.Impl.Sm4.PPC64LE.Prepared
import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit
public import VerifiedGarbage.Proof.Sm4.Prepared

/-!
# SM4's prepared round keys and batches on PPC64LE: the code

What `vg_sm4_prepare_keys` writes (`layout`, `Proof.Sm4.Prepared.Holds`) is
the masks and the table that ECB's rounds read (`ReadyAt`), word for word
(`WordsAt`, `holds_iff_words`, `readyAt_iff_words`): each of the table's
words is the plane of its round key (`planeOf`, the only words related to
it by `WordRel`, `wordRel_eq`).

`prepareBody_wp` and `cryptBody_wp` run the two functions' bodies, with their
working space exactly ECB's scratch buffer: ECB's prologue, the key setup
(`keys_wp`) or the sixteen blocks (`crypt16_wp`), and the epilogue.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (sb t0 movR stS)
open VG.Proof.Sm4 (WordRel specDirA)

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

theorem ofSpecDir_specDirA (d : Dir) : ofSpecDir (specDirA d) = d := by cases d <;> rfl

/-- The masks and the table of round keys in the order of `d`: what ECB's
rounds read. -/
def ReadyAt (d : Dir) (m : Mem) (B : Addr) (k : Spec.Sm4.Schedule) : Prop :=
  MasksAt m B ∧ ∀ e < 32, WordRel (entryW m B e) fun _ => dirKeys d k e

/-- The words `vg_sm4_prepare_keys` writes, in the working space at `B`. -/
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

/-! ## The bodies -/

/-- `vg_sm4_prepare_keys`'s body, with its working space at `r5` exactly
ECB's scratch buffer. -/
theorem prepareBody_wp {s₀ : State} (hrd : s₀.rd = [⟨s₀.gpr .r3, 128⟩]) (hwr : s₀.wr = [⟨s₀.gpr .r5, 8 * slots⟩])
    (dSS : Region.Disjoint ⟨s₀.gpr .r3, 128⟩ ⟨s₀.gpr .r5, 8 * slots⟩)
    (fitK : (s₀.gpr .r3).toNat + 128 ≤ 2 ^ 64) (fitB : (s₀.gpr .r5).toNat + 8 * slots ≤ 2 ^ 64) :
    WP isa prepareKeys s₀ fun s' => (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      WordsAt s'.mem (s₀.gpr .r5) (Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .r3)) (dirOf (s₀.gpr .r4)) := by
  let b := s₀.gpr .r5
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hrK : (⟨s₀.gpr .r3, 128⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, m₁, f₁, rd₁, wr₁⟩ := prologue_ok (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : SchedPre s₁ b (s₀.gpr .r3) :=
    ⟨b₁, by rw [wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have r3₁ : s₁.gpr .r3 = s₀.gpr .r3 := g₁ _ (by decide) (by decide)
  have r4₁ : s₁.gpr .r4 = s₀.gpr .r4 := g₁ _ (by decide) (by decide)
  have hsch : Spec.Sm4.scheduleAt s₁.mem (s₀.gpr .r3) = Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .r3) :=
    hk₁.sched_eq' (Nat.le_refl _) f₁
  refine WP.seq (WP.mono (Q := KeysPost s₁ b (s₀.gpr .r3) (dirOf (s₀.gpr .r4))) ?_ fun s₂ k₂ => ?_)
  · by_cases h0 : s₀.gpr .r4 = 0
    · have : dirOf (s₀.gpr .r4) = .encrypt := by simp only [dirOf, h0, ite_true]
      rw [this]
      refine WP.seq (WP.ite false (by rw [eval_nonzero, r4₁, h0]; rfl) (fun h => by cases h)
        fun _ => WP.of_runBlock ⟨_, rfl, ?_⟩)
      exact WP.ite true (by rw [eval_zero, r4₁, h0]; rfl) (fun _ => keys_wp .encrypt hk₁ r3₁ m₁)
        fun h => by cases h
    · have : dirOf (s₀.gpr .r4) = .decrypt := by simp only [dirOf, h0, ite_false]
      rw [this]
      refine WP.seq (WP.ite true (by rw [eval_nonzero, r4₁]; simpa using h0) (fun _ =>
        WP.mono (keys_wp .decrypt hk₁ r3₁ m₁) fun s k => ?_) fun h => by cases h)
      have r4 : s.gpr .r4 = s₀.gpr .r4 := by
        rw [k.regs .r4 (by decide) (by decide) (by decide) (by decide), r4₁]
      exact WP.ite false (by rw [eval_zero, r4]; simpa using h0) (fun h => by cases h) fun _ => WP.of_runBlock ⟨_, rfl, k⟩
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have sv₂ : Saved s₀ b s₂.mem := fun i hi => by
    rw [← sv₁ i hi]
    refine k₂.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [tableEnd_eq, savedSlot_eq]; omega_arith)
      (by rw [savedSlot_eq]; omega_arith)
  obtain ⟨s₃, e₃, rg₃, -, m₃, -, -⟩ := restore_ok (by rw [k₂.wr, wr₁]; exact hwS) base₂ sv₂
  refine WP.of_runBlock ⟨s₃, e₃, rg₃, ?_⟩
  rw [m₃, ← hsch]
  exact words_of_readyAt ⟨k₂.masks.at base₂, fun e he => by
    have := k₂.key.keys e he; rw [base₂] at this; exact this⟩

/-- The rounds with the round keys in the order of `d` are its cipher. -/
theorem quads_spec (d : Dir) (sch : Spec.Sm4.Schedule) (blk : Spec.Sm4.Block) :
    Proof.Sm4.outBlock (Proof.Sm4.quads .enc (dirKeys d sch) 8 (Proof.Sm4.ofBlock blk)) =
      Proof.Sm4.blockFn sch (specDirA d) blk := by
  cases d
  · simp only [Proof.Sm4.blockFn, specDirA, Spec.Sm4.encryptBlock, Proof.Sm4.crypt_eq]; rfl
  · simp only [Proof.Sm4.blockFn, specDirA, Spec.Sm4.decryptBlock, Proof.Sm4.crypt_eq]; rfl

/-- The registers' saves write their slots alone. -/
theorem save_saved {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b + BitVec.ofNat 64 (8 * savedSlot), 144⟩] s.mem s'.mem := by
  let L : List (Nat × Reg) := (List.range 18).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs = L.map fun x => stS x.1 x.2 := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 18).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  have hw' := hw
  rw [slots_eq] at hw'
  obtain ⟨s', e', g', rd', wr', f', -, v'⟩ := stS_list_ok ⟨b + BitVec.ofNat 64 (8 * savedSlot), 144⟩ L s
    (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨by rw [savedSlot_eq]; omega_arith, ⟨_, hw', ?_⟩, ?_⟩
      · rw [hb]; exact VG.Offset.contains_base b (by rw [savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
      · rw [hb, wordAddr]
        exact VG.Offset.contains b (by rw [savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
          (by rw [savedSlot_eq]; omega_arith))
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, g', rd', wr', f'⟩
  have := v' (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
  simp only [slotW, g', hb] at this
  exact this

/-- `vg_sm4_crypt_prepared`'s body, with its working space at `r3` ECB's
scratch buffer, holding the round keys `k` in the order of `d`. -/
theorem cryptBody_wp {s₀ : State} (hwr : (⟨s₀.gpr .r3, 8 * slots⟩ : Region) ∈ s₀.wr)
    (fitB : (s₀.gpr .r3).toNat + 8 * slots ≤ 2 ^ 64) {k : Spec.Sm4.Schedule} {d : Dir}
    (hr : ReadyAt d s₀.mem (s₀.gpr .r3) k) :
    WP isa cryptPrepared s₀ fun s' => (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      ReadyAt d s'.mem (s₀.gpr .r3) k ∧
      Frame [⟨s₀.gpr .r3, 8 * tableSlot⟩, ⟨s₀.gpr .r3 + BitVec.ofNat 64 (8 * savedSlot), 144⟩] s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      ∀ j < 16, Spec.Sm4.blockAt s'.mem (s₀.gpr .r3 + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        Proof.Sm4.blockFn k (specDirA d) (Spec.Sm4.blockAt s₀.mem (s₀.gpr .r3 + BitVec.ofNat 64 (8 * tailSlot + 16 * j))) := by
  generalize hb : s₀.gpr .r3 = b at hwr fitB hr ⊢
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .r3
  have b₁ : s₁.gpr sb = b := r₁.trans hb
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_saved (b := b) (by rw [wr₁]; exact hwr) b₁
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := slotAddr_ok s₂ .r11 tableEnd (by decide)
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
  obtain ⟨s₅, e₅, rg₅, -, m₅, rd₅, wr₅⟩ := restore_ok (by rw [c₄.wr, wr₃, wr₂, wr₁]; exact hwr) base₄ sv₄
  refine WP.of_runBlock ⟨s₅, e₅, fun i hi => by rw [rg₅ i hi, o₁ _ (sreg_ne i hi)], ?_, ?_,
    by rw [rd₅, c₄.rd, rd₃, rd₂, rd₁], by rw [wr₅, c₄.wr, wr₃, wr₂, wr₁], fun j hj => ?_⟩
  · refine ⟨fun kv hkv => by rw [m₅]; exact c₄.masks.at base₄ kv hkv, fun e he => (hr.2 e he).congr fun j hj => ?_⟩
    rw [entryW_eq, entryW_eq, m₅, ← slot₃ (tableSlot + 8 * e + j) (by rw [tableSlot_eq, savedSlot_eq]; omega_arith)]
    refine f₄.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (by first | omega_arith | (rw [tableSlot_eq]; omega_arith))
      (by first | omega_arith | (rw [tableSlot_eq]; omega_arith))
  · rw [m₅]
    have l₂ : Frame [⟨b, 8 * tableSlot⟩, ⟨b + BitVec.ofNat 64 (8 * savedSlot), 144⟩] s₀.mem s₃.mem := by
      rw [m₃, ← m₁]
      exact f₂.sub fun r hr => ⟨⟨b + BitVec.ofNat 64 (8 * savedSlot), 144⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub b (d := 8 * savedSlot) (n := 144) (e := 8 * savedSlot) (k := 144) (by omega_arith) (by omega_arith)⟩
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

end VG.Proof.Sm4.PPC64LE
