module

public import VerifiedGarbage.Proof.Camellia.AArch64.Ecb
import VerifiedGarbage.Proof.Camellia.AArch64.Crypt8
public import VerifiedGarbage.Impl.Camellia.AArch64.Prepared
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Camellia's prepared subkeys and batches on AArch64: the code

What `vg_camellia_prepare_keys` writes (`layout`,
`Spec.Camellia.Prepared.Holds`) is the masks and the table that ECB's rounds
read (`ReadyAt`), word for word (`TableWordsAt`, `holds_of_words`,
`readyAt_of_words` and back): each of the table's words is the plane of its
subkey (`keyPlane`, the only words related to it by `HalfRel`,
`halfRel_eq`).

`prepareBody_wp` and `cryptBody_wp` run the two functions' bodies, with
their working space exactly ECB's scratch buffer: ECB's prologue, the key
setup (`keys_wp`) or the eight blocks (`crypt8_ok`), and the epilogue.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (sb t0 t1 kp movR stS)
open VG.Impl.Camellia (keyPlane)
open VG.Proof.Camellia (HalfRel schedWords_getD wordAt_frame dirPerm_lt blockFn)

/-! ## The encoding -/

/-- The planes of a subkey hold it. -/
theorem keyPlane_rel (x : BitVec 64) : HalfRel (keyPlane x) fun _ => x :=
  fun _ hb _ hc _ hj => Proof.Camellia.sigma_planes x hb hc hj

/-- The only planes of the subkey `x` are `keyPlane x`. -/
theorem halfRel_eq {Q : Nat → BitVec 64} {x : BitVec 64} (h : HalfRel Q fun _ => x) {j : Nat} (hj : j < 8) :
    Q j = keyPlane x j := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have e1 := h (p % 8) (by omega) (p / 8) (by omega) j hj
  have e2 := keyPlane_rel x (p % 8) (by omega) (p / 8) (by omega) j hj
  rw [show 8 * (p / 8) + p % 8 = p by omega] at e1 e2
  rw [e1, e2]

theorem keyEntry_eq (w : List (BitVec 64)) (g : Nat) (d : Dir) (e : Nat) :
    keyEntry w g d e = w.getD (permOf d g e) 0 := by
  cases d <;> rfl

theorem ofSpecDir_specDir (d : Dir) : ofSpecDir (specDir d) = d := by cases d <;> rfl

theorem specDir_ofSpecDir (d : Spec.Camellia.Direction) : specDir (ofSpecDir d) = d := by cases d <;> rfl

/-- The direction `vg_camellia_prepare_keys`'s `decrypt` selects. -/
def dirOf (decrypt : BitVec 64) : Dir := if decrypt = 0 then .encrypt else .decrypt

theorem specDir_dirOf (decrypt : BitVec 64) :
    specDir (dirOf decrypt) = Spec.Camellia.Prepared.directionOf decrypt.toNat := by
  unfold dirOf Spec.Camellia.Prepared.directionOf
  by_cases h : decrypt = 0
  · subst h; rfl
  · have h' : decrypt.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    simp only [h, h', ite_false]; rfl

/-- The masks and the table of subkeys of `R` rounds in the order of `d`:
what ECB's rounds read. -/
def ReadyAt (d : Dir) (R : Nat) (m : Mem) (B : Addr) (w : List (BitVec 64)) : Prop :=
  MasksAt m B ∧ ∀ i < 8 * (R / 6) + 2, EntryOk m B i (keyEntry w (R / 6) d i)

/-- The words `vg_camellia_prepare_keys` writes for `R` rounds, in the
working space at `B`. -/
def TableWordsAt (R : Nat) (m : Mem) (B : Addr) (w : List (BitVec 64)) (d : Dir) : Prop :=
  ∀ k, (evenSlot ≤ k ∧ k ≤ m3Slot) ∨ (keySlot ≤ k ∧ k < keySlot + 8 * (8 * (R / 6) + 2)) →
    m.readW (wordAddr B k) 64 = preparedWord R w d k

/-- Byte `j` of a word. -/
theorem byte_of_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    m (a + BitVec.ofNat 64 j) = (m.readW a 64).extractLsb' (8 * j) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

theorem word_byte_addr (B : Addr) (o : Nat) : B + BitVec.ofNat 64 o = wordAddr B (o / 8) + BitVec.ofNat 64 (o % 8) := by
  rw [wordAddr, VG.Offset.add_add]
  congr 2; omega

theorem layout_table (R : Nat) : layout.table R = [(384, 40), (768, 64 * (8 * (R / 6) + 2))] := rfl
theorem evenSlot_eq : evenSlot = 48 := rfl
theorem m3Slot_eq : m3Slot = 52 := rfl

theorem table_ranges (R o : Nat) :
    (∃ r ∈ layout.table R, ∃ i < r.2, o = r.1 + i) ↔
      (evenSlot ≤ o / 8 ∧ o / 8 ≤ m3Slot) ∨ (keySlot ≤ o / 8 ∧ o / 8 < keySlot + 8 * (8 * (R / 6) + 2)) := by
  rw [layout_table, evenSlot_eq, m3Slot_eq, keySlot_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨r, hr | hr, i, hi, rfl⟩ <;> subst hr <;> dsimp only at hi ⊢ <;> omega
  · intro h
    rcases h with h | h
    · exact ⟨_, .inl rfl, o - 384, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨_, .inr rfl, o - 768, by dsimp only; omega, by dsimp only; omega⟩

theorem holds_of_words {R : Nat} {m : Mem} {B : Addr} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (h : TableWordsAt R m B w (ofSpecDir d)) : Spec.Camellia.Prepared.Holds layout m B R w d := by
  intro r hr i hi
  have hw := (table_ranges R (r.1 + i)).1 ⟨r, hr, i, hi, rfl⟩
  rw [word_byte_addr, byte_of_readW m _ (by omega), h _ hw]
  rfl

theorem words_of_holds {R : Nat} {m : Mem} {B : Addr} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (h : Spec.Camellia.Prepared.Holds layout m B R w d) : TableWordsAt R m B w (ofSpecDir d) := by
  intro k hk
  simp only [Mem.readW, BitVec.setWidth_eq]
  refine Mem.read_eq_of_bytes fun j hj => ?_
  obtain ⟨r, hr, i, hi, ho⟩ := (table_ranges R (8 * k + j)).2 (by
    rw [show (8 * k + j) / 8 = k by omega]; exact hk)
  have := h r hr i hi
  rw [← ho, word_byte_addr, show (8 * k + j) / 8 = k by omega, show (8 * k + j) % 8 = j by omega] at this
  rw [this]
  show (preparedWord R w (ofSpecDir d) ((8 * k + j) / 8)).extractLsb' (8 * ((8 * k + j) % 8)) 8 = _
  rw [show (8 * k + j) / 8 = k by omega, show (8 * k + j) % 8 = j by omega]

theorem entryW_eq (m : Mem) (B : Addr) (e j : Nat) :
    entryW m B e j = m.readW (wordAddr B (keySlot + 8 * e + j)) 64 := by
  rw [entryW, wordAddr, show 8 * (keySlot + 8 * e + j) = 8 * keySlot + 64 * e + 8 * j by omega]

theorem preparedWord_entry (R : Nat) (w : List (BitVec 64)) (d : Dir) {e j : Nat} (hj : j < 8) :
    preparedWord R w d (keySlot + 8 * e + j) = keyPlane (keyEntry w (R / 6) d e) j := by
  have hc : ¬ (keySlot + 8 * e + j < keySlot) := by omega
  simp only [preparedWord, hc, ↓reduceIte]
  rw [show (keySlot + 8 * e + j - keySlot) / 8 = e by omega, show (keySlot + 8 * e + j - keySlot) % 8 = j by omega]

theorem preparedWord_mask (R : Nat) (w : List (BitVec 64)) (d : Dir) {kv : Nat × BitVec 64}
    (hkv : kv ∈ layerMasks) : preparedWord R w d kv.1 = kv.2 := by
  simp only [layerMasks, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem mask_in {kv : Nat × BitVec 64} (hkv : kv ∈ layerMasks) : evenSlot ≤ kv.1 ∧ kv.1 ≤ m3Slot := by
  simp only [layerMasks, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl | rfl | rfl | rfl <;> decide

theorem readyAt_of_words {R : Nat} {m : Mem} {B : Addr} {w : List (BitVec 64)} {d : Dir}
    (h : TableWordsAt R m B w d) : ReadyAt d R m B w := by
  refine ⟨fun kv hkv => by rw [h _ (.inl (mask_in hkv)), preparedWord_mask R w d hkv], fun e he => ?_⟩
  refine (keyPlane_rel (keyEntry w (R / 6) d e)).congr fun j hj => ?_
  rw [entryW_eq, h _ (.inr (by omega)), preparedWord_entry R w d hj]

theorem words_of_readyAt {R : Nat} {m : Mem} {B : Addr} {w : List (BitVec 64)} {d : Dir}
    (h : ReadyAt d R m B w) : TableWordsAt R m B w d := by
  intro k hk
  rcases hk with hk | hk
  · have hkv : ∃ kv ∈ layerMasks, kv.1 = k := by
      rw [evenSlot_eq, m3Slot_eq] at hk
      simp only [layerMasks, List.mem_cons, List.not_mem_nil, or_false]
      rcases (by omega : k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52) with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, .inl rfl, rfl⟩
      · exact ⟨_, .inr (.inl rfl), rfl⟩
      · exact ⟨_, .inr (.inr (.inl rfl)), rfl⟩
      · exact ⟨_, .inr (.inr (.inr (.inl rfl))), rfl⟩
      · exact ⟨_, .inr (.inr (.inr (.inr rfl))), rfl⟩
    obtain ⟨kv, hkv, rfl⟩ := hkv
    rw [h.1 kv hkv, preparedWord_mask R w d hkv]
  · obtain ⟨e, j, hj, rfl⟩ : ∃ e j, j < 8 ∧ k = keySlot + 8 * e + j :=
      ⟨(k - keySlot) / 8, (k - keySlot) % 8, by omega, by omega⟩
    have he : e < 8 * (R / 6) + 2 := by omega
    rw [← entryW_eq, preparedWord_entry R w d hj]
    exact halfRel_eq (h.2 e he) hj

/-- The rounds with the subkeys in the order of `d` are its block function. -/
theorem crypt_spec (d : Dir) {R : Nat} (hR : R = 18 ∨ R = 24) (w : List (BitVec 64)) (blk : Spec.Camellia.Block) :
    Spec.Camellia.encodeBlock (cryptWords (R / 6) (keyEntry w (R / 6) d) (Spec.Camellia.decodeBlock blk)) =
      blockFn (Spec.Camellia.subkeysOfWords R w) (specDir d) blk := by
  cases d
  · simp only [blockFn, specDir, Spec.Camellia.encryptBlock, encryptWith_eq hR]; rfl
  · simp only [blockFn, specDir, Spec.Camellia.decryptBlock, decryptWith_eq hR]; rfl

/-! ## The bodies -/

/-- `vg_camellia_prepare_keys`'s body, with its working space at `x3`
exactly ECB's scratch buffer. -/
theorem prepareBody_wp {s₀ : State} (hrd : s₀.rd = [⟨s₀.gpr .x0, 272⟩]) (hwr : s₀.wr = [⟨s₀.gpr .x3, 8 * slots⟩])
    (dSS : Region.Disjoint ⟨s₀.gpr .x0, 272⟩ ⟨s₀.gpr .x3, 8 * slots⟩)
    (fitK : (s₀.gpr .x0).toNat + 272 ≤ 2 ^ 64) (fitB : (s₀.gpr .x3).toNat + 8 * slots ≤ 2 ^ 64)
    (hR : (s₀.gpr .x1).toNat = 18 ∨ (s₀.gpr .x1).toNat = 24) :
    WP isa prepareKeys s₀ fun s' => (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      TableWordsAt (s₀.gpr .x1).toNat s'.mem (s₀.gpr .x3)
        (Spec.Camellia.Prepared.wordsAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat) (dirOf (s₀.gpr .x2)) := by
  let b := s₀.gpr .x3
  let sched := s₀.gpr .x0
  let R := (s₀.gpr .x1).toNat
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hrK : (⟨sched, 272⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, m₁, t₁, f₁, rd₁, wr₁⟩ := prologue_ok (a := .x3) (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : KeyPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have x0₁ : s₁.gpr .x0 = sched := g₁ _ (by decide) (by decide)
  have x2₁ : s₁.gpr .x2 = s₀.gpr .x2 := g₁ _ (by decide) (by decide)
  have hz₁ : (s₁.gpr t0 == 0) = decide (R = 18) := by
    rw [t₁, show s₀.gpr .x1 = BitVec.ofNat 64 R by simp only [R, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  have hz : isa.eval (.zero .x t0) s₁ = some (decide (g = 3)) := (eval_zero s₁ t0).trans (by
    rw [hz₁]; exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩))
  have hfitB := fitB
  rw [slots_eq] at hfitB
  refine WP.seq (WP.mono (Q := fun s₂ => KeysPost s₁ b sched g (permOf (dirOf (s₀.gpr .x2)) g) s₂) ?_ fun s₂ k₂ => ?_)
  · refine WP.ite (s₀.gpr .x2 == 0) ((eval_zero s₁ .x2).trans (by rw [x2₁])) (fun h => ?_) (fun h => ?_)
    · have : dirOf (s₀.gpr .x2) = .encrypt := by simp only [dirOf, beq_iff_eq.mp h, ite_true]
      rw [this]; exact WP.mono (keys_wp .encrypt hg hz hk₁ x0₁ m₁) fun _ h => h.1
    · have h' : s₀.gpr .x2 ≠ 0 := fun e => by rw [e] at h; exact absurd h (by decide)
      have : dirOf (s₀.gpr .x2) = .decrypt := by simp only [dirOf, h', ite_false]
      rw [this]; exact WP.mono (keys_wp .decrypt hg hz hk₁ x0₁ m₁) fun _ h => h.1
  have base₂ : s₂.gpr sb = b := k₂.pre.base
  have sv₂ : Saved s₀ b s₂.mem := fun i hi => by
    rw [← sv₁ i hi]
    refine k₂.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [endSlot_eq, savedSlot_eq]; omega)
      (by rw [savedSlot_eq]; omega)
  obtain ⟨s₃, e₃, rg₃, -, m₃, -, -⟩ := restore_ok (by rw [k₂.wr, wr₁]; exact hwS) base₂ sv₂
  refine WP.of_runBlock ⟨s₃, e₃, rg₃, ?_⟩
  rw [m₃]
  refine words_of_readyAt ⟨k₂.masks.at base₂, fun i hi => ?_⟩
  rw [hgR] at hi ⊢
  have := k₂.ent i hi
  have hp : permOf (dirOf (s₀.gpr .x2)) g i < 8 * g + 2 := dirPerm_lt _ hi
  have hl : permOf (dirOf (s₀.gpr .x2)) g i < Spec.Camellia.scheduleLength R := by
    simp only [Spec.Camellia.scheduleLength]; omega
  rw [keyEntry_eq]
  show EntryOk s₂.mem b i ((Proof.Camellia.schedWords s₀.mem sched R).getD _ 0)
  rw [schedWords_getD _ _ hl]
  rw [wordAt_frame f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dSS.sub_left (VG.Offset.sub_base sched (by simp only [Spec.Camellia.scheduleLength] at hl; omega))).sub_right
        (Region.sub_prefix (by rw [keySlot_eq, slots_eq]; omega))
    · exact (dSS.sub_left (VG.Offset.sub_base sched (by simp only [Spec.Camellia.scheduleLength] at hl; omega))).sub_right
        (VG.Offset.sub_base b (by rw [savedSlot_eq, slots_eq]; omega))] at this
  exact this

/-- The entry of the postwhitening subkey, for `g` groups. -/
theorem endAddr_ok (s : State) {g : Nat} (hg : g = 3 ∨ g = 4) :
    ∃ s', runBlock isa (endAddr g) s = some s' ∧
      s'.gpr .x4 = s.gpr sb + BitVec.ofNat 64 (8 * keySlot + 512 * g) ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .x4 sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ .x4 .x4 (imm := 8 * keySlot + 512 * g)
    (by rw [keySlot_eq]; omega)
  refine ⟨s₂, ?_, by rw [r₂, r₁], fun r h => by rw [o₂ r h, o₁ r h], by rw [m₂, m₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  rw [endAddr, show ([movR .x4 sb, .addImm .x .x4 .x4 (8 * keySlot + 512 * g)] :
    List Instr) = [movR .x4 sb] ++ [.addImm .x .x4 .x4 (8 * keySlot + 512 * g)] from rfl,
    runBlock_append', e₁, Option.bind_some, e₂]

/-- `vg_camellia_crypt_prepared`'s body, with its working space at `x1`
ECB's scratch buffer, holding the subkeys of the words `w` of `x0`'s
rounds in the order of `d`. -/
theorem cryptBody_wp {s₀ : State} (hwr : (⟨s₀.gpr .x1, 8 * slots⟩ : Region) ∈ s₀.wr)
    (fitB : (s₀.gpr .x1).toNat + 8 * slots ≤ 2 ^ 64) (hR : (s₀.gpr .x0).toNat = 18 ∨ (s₀.gpr .x0).toNat = 24)
    {w : List (BitVec 64)} {d : Dir} (hr : ReadyAt d (s₀.gpr .x0).toNat s₀.mem (s₀.gpr .x1) w) :
    WP isa cryptPrepared s₀ fun s' => (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      ReadyAt d (s₀.gpr .x0).toNat s'.mem (s₀.gpr .x1) w ∧
      Frame [⟨s₀.gpr .x1, 8 * keySlot⟩, ⟨s₀.gpr .x1 + BitVec.ofNat 64 (8 * savedSlot), 208⟩] s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      ∀ j < 8, Spec.Camellia.blockAt s'.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        blockFn (Spec.Camellia.subkeysOfWords (s₀.gpr .x0).toNat w) (specDir d)
          (Spec.Camellia.blockAt s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 (8 * tailSlot + 16 * j))) := by
  generalize hb : s₀.gpr .x1 = b at hwr fitB hr ⊢
  let R := (s₀.gpr .x0).toNat
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .x1
  have b₁ : s₁.gpr sb = b := r₁.trans hb
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁]; exact hwr) b₁
  obtain ⟨s₃, e₃, t₃, o₃, m₃, rd₃, wr₃⟩ := subI_ok s₂ t0 .x0 (imm := 18) (by decide)
  have b₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), g₂, b₁]
  have hz₃ : isa.eval (.zero .x t0) s₃ = some (decide (g = 3)) := by
    rw [eval_zero, t₃, g₂, o₁ _ (by decide),
      show s₀.gpr .x0 = BitVec.ofNat 64 R by simp only [R, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩)
  have hfit := fitB
  rw [slots_eq] at hfit
  have slot₃ : ∀ k < savedSlot, s₃.mem.readW (wordAddr b k) 64 = s₀.mem.readW (wordAddr b k) 64 := fun k hk => by
    rw [m₃, ← m₁]
    refine f₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint b (.inl (by rw [savedSlot_eq] at hk ⊢; omega)) (by rw [savedSlot_eq] at hk; omega)
      (by rw [savedSlot_eq]; omega)
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃], ?_⟩)
  -- The postwhitening's entry.
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => s₄.gpr .x4 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) ∧
      (∀ r, r ≠ .x4 → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr)
    (WP.ite (decide (g = 3)) hz₃ (fun h => ?_) (fun h => ?_)) fun s₄ ⟨x4₄, o₄, m₄, rd₄, wr₄⟩ => ?_)
  · have hg3 : g = 3 := of_decide_eq_true h
    obtain ⟨s', e', x4', o', m', rd', wr'⟩ := endAddr_ok s₃ (g := 3) (.inl rfl)
    exact WP.of_runBlock ⟨s', e', by rw [x4', b₃, hg3], o', m', rd', wr'⟩
  · have hg4 : g = 4 := by have := of_decide_eq_false h; omega
    obtain ⟨s', e', x4', o', m', rd', wr'⟩ := endAddr_ok s₃ (g := 4) (.inr rfl)
    exact WP.of_runBlock ⟨s', e', by rw [x4', b₃, hg4], o', m', rd', wr'⟩
  have b₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), b₃]
  have hcore : CorePre s₄ g (keyEntry w g d) :=
    { scr := by rw [b₄, wr₄, wr₃, wr₂, wr₁]; exact hwr
      fit := by rw [b₄]; exact fitB
      nk34 := by omega
      masks := fun kv hkv => by
        show s₄.mem.readW (wordAddr (s₄.gpr sb) kv.1) 64 = kv.2
        rw [b₄, m₄, slot₃ _ (by have := mask_in hkv; rw [m3Slot_eq] at this; rw [savedSlot_eq]; omega)]
        exact hr.1 kv hkv
      keys := fun i hi => by
        have := hr.2 i (by rw [hgR]; exact hi)
        rw [hgR] at this
        refine this.congr fun j hj => ?_
        rw [b₄, entryW_eq, entryW_eq, m₄, slot₃ _ (by rw [keySlot_eq, savedSlot_eq]; omega)]
      hg := hg
      bound := by rw [x4₄, b₄] }
  refine WP.seq (WP.mono (crypt8_ok hcore) fun s₅ ⟨c₅, o₅⟩ => ?_)
  have base₅ : s₅.gpr sb = b := by rw [c₅.base, b₄]
  have f₅ : Frame (ctxRegions b) s₄.mem s₅.mem := by have := c₅.frame; rw [b₄] at this; exact this
  have sv₅ : Saved s₁ b s₅.mem := fun i hi => by
    rw [← sv₂ i hi, ← m₃, ← m₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [keySlot_eq, savedSlot_eq]; omega)
        (by rw [savedSlot_eq]; omega)
    · exact VG.Offset.disjoint b (.inl (by rw [savedSlot_eq, tailSlot_eq]; omega)) (by rw [savedSlot_eq]; omega)
        (by rw [tailSlot_eq]; omega)
  obtain ⟨s₆, e₆, rg₆, -, m₆, rd₆, wr₆⟩ := restore_ok (by rw [c₅.wr, wr₄, wr₃, wr₂, wr₁]; exact hwr) base₅ sv₅
  have hk5 : ∀ k, keySlot ≤ k → k < savedSlot →
      s₅.mem.readW (wordAddr b k) 64 = s₀.mem.readW (wordAddr b k) 64 := fun k h1 h2 => by
    rw [← slot₃ k h2, ← m₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by omega) (by rw [savedSlot_eq] at h2; omega)
    · exact VG.Offset.disjoint b (.inl (by rw [savedSlot_eq, tailSlot_eq] at *; omega))
        (by rw [savedSlot_eq] at h2; omega) (by rw [tailSlot_eq]; omega)
  refine WP.of_runBlock ⟨s₆, e₆, fun i hi => by rw [rg₆ i hi, o₁ _ (sreg_ne i hi)], ?_, ?_,
    by rw [rd₆, c₅.rd, rd₄, rd₃, rd₂, rd₁], by rw [wr₆, c₅.wr, wr₄, wr₃, wr₂, wr₁], fun j hj => ?_⟩
  · refine ⟨fun kv hkv => by rw [m₆]; exact c₅.masks.at base₅ kv hkv, fun i hi => (hr.2 i hi).congr fun j hj => ?_⟩
    have hg4 : (s₀.gpr .x0).toNat / 6 ≤ 4 := by omega
    rw [entryW_eq, entryW_eq, m₆, hk5 _ (by omega) (by rw [keySlot_eq, savedSlot_eq]; omega)]
  · rw [m₆]
    have l₄ : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * savedSlot), 208⟩] s₀.mem s₄.mem := by
      rw [m₄, m₃, ← m₁]
      exact f₂.sub fun r hr => ⟨⟨b + BitVec.ofNat 64 (8 * savedSlot), 208⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub b (d := 8 * savedSlot) (n := 80) (e := 8 * savedSlot) (k := 208) (by omega) (by omega)⟩
    exact l₄.trans (f₅.sub fun r hr => by
      simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
          VG.Offset.sub b (by rw [savedSlot_eq, tailSlot_eq] <;> omega) (by rw [savedSlot_eq, tailSlot_eq] <;> omega)⟩)
  · have := o₅ j hj
    simp only [blk, base₅, b₄] at this
    rw [m₆, this, ← hgR, crypt_spec d hR, m₄, m₃]
    refine congrArg _ (Vector.ext fun i hi => ?_)
    simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn]
    rw [show b + BitVec.ofNat 64 (8 * tailSlot + 16 * j) + BitVec.ofNat 64 i =
      b + BitVec.ofNat 64 (8 * tailSlot) + BitVec.ofNat 64 (16 * j + i) by
        rw [VG.Offset.add_add, VG.Offset.add_add]; congr 2; omega, ← m₁]
    refine f₂.bytes (R := ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩) (fun r hr => ?_) (by show (128 : Nat) ≤ 2 ^ 64; decide)
      (by show 16 * j + i < 128; omega)
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨b + BitVec.ofNat 64 (8 * savedSlot), 80⟩
    exact VG.Offset.disjoint b (.inr (by rw [savedSlot_eq, tailSlot_eq] <;> omega)) (by rw [tailSlot_eq] <;> omega)
      (by rw [savedSlot_eq]; omega)

end VG.Proof.Camellia.AArch64
