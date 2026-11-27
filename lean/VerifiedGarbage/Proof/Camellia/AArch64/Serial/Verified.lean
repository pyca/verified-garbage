module

import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Crypt
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Camellia.Prepared
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Modes.AArch64.Steps
public import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Camellia.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Crypt
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Camellia.Prepared
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Camellia.Common
meta import VerifiedGarbage.Proof.Camellia.CtrCipher
meta import VerifiedGarbage.Proof.Camellia.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Prepared
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.State
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Proof.Camellia.Bitsliced
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Camellia.AArch64.Serial.State
meta import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Prepared
meta import VerifiedGarbage.Proof.Camellia.Bitsliced
import VerifiedGarbage.Proof.Camellia.AArch64.Group
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Framework.AArch64.Straight
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Camellia
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Sm4.AArch64.Imm
import VerifiedGarbage.Proof.Sm4.AArch64.Prologue
public import VerifiedGarbage.Proof.Sm4.AArch64.Round
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Modes.AArch64.ViaV
public import VerifiedGarbage.Impl.Camellia.AArch64.Ctr
public import VerifiedGarbage.Spec.Camellia.Cbc
import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Camellia.AArch64.Ecb
import VerifiedGarbage.Proof.Camellia.AArch64.Crypt8
public import VerifiedGarbage.Impl.Camellia.AArch64.Prepared
meta import VerifiedGarbage.Proof.Camellia.AArch64.Ecb
meta import VerifiedGarbage.Proof.Camellia.AArch64.Crypt8
meta import VerifiedGarbage.Impl.Camellia.AArch64.Prepared
meta import VerifiedGarbage.Proof.Camellia.AArch64.Group
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Core
meta import VerifiedGarbage.Proof.Framework.AArch64.Straight
meta import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Spec.Camellia
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Sm4.AArch64.Imm
meta import VerifiedGarbage.Proof.Sm4.AArch64.Prologue
meta import VerifiedGarbage.Proof.Sm4.AArch64.Round
meta import VerifiedGarbage.Proof.Framework.Interleave
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Modes.AArch64.ViaV
meta import VerifiedGarbage.Impl.Camellia.AArch64.Ctr
meta import VerifiedGarbage.Spec.Camellia.Cbc
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! ### `Camellia.AArch64.Serial.Prepared`, which this module and modules that import it used -/

section

/-! ### `Camellia.AArch64.ModeCore`, which this module and modules that import it used -/

section

/-! ### `Camellia.AArch64.PreparedVerified`, which only this module used -/

section

/-! ### `Camellia.AArch64.PreparedBody`, which this module and modules that import it used -/

section

/-!
# Camellia's prepared subkeys and batches on AArch64: the code

What `vg_camellia_prepare_keys` writes (`layout`,
`Proof.Camellia.Prepared.Holds`) is the masks and the table that ECB's rounds
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

/-- The masks' slots and the table's, as byte ranges. -/
def layout : Prepared.Layout where
  table rounds := [(8 * evenSlot, 40), (8 * keySlot, 64 * (8 * (rounds / 6) + 2))]
  encode rounds w d i := (preparedWord rounds w (ofSpecDir d) (i / 8)).extractLsb' (8 * (i % 8)) 8
  buf := 8 * tailSlot
  blocks := 8
  prepScratch := [(0, 8 * slots)]
  cryptScratch := [(0, 8 * evenSlot), (8 * (m3Slot + 1), 8 * (keySlot - m3Slot - 1)),
    (8 * savedSlot, 8 * (tailSlot + 16 - savedSlot))]
  size := 8 * slots

/-! ## The encoding -/

/-- The planes of a subkey hold it. -/
theorem keyPlane_rel (x : BitVec 64) : HalfRel (keyPlane x) fun _ => x :=
  fun _ hb _ hc _ hj => Proof.Camellia.sigma_planes x hb hc hj

/-- The only planes of the subkey `x` are `keyPlane x`. -/
theorem halfRel_eq {Q : Nat → BitVec 64} {x : BitVec 64} (h : HalfRel Q fun _ => x) {j : Nat} (hj : j < 8) :
    Q j = keyPlane x j := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have e1 := h (p % 8) (by omega_arith) (p / 8) (by omega_arith) j hj
  have e2 := keyPlane_rel x (p % 8) (by omega_arith) (p / 8) (by omega_arith) j hj
  rw [show 8 * (p / 8) + p % 8 = p by omega_arith] at e1 e2
  rw [e1, e2]

theorem keyEntry_eq (w : List (BitVec 64)) (g : Nat) (d : Dir) (e : Nat) :
    keyEntry w g d e = w.getD (permOf d g e) 0 := by
  cases d <;> rfl

theorem ofSpecDir_specDir (d : Dir) : ofSpecDir (specDir d) = d := by cases d <;> rfl

theorem specDir_ofSpecDir (d : Spec.Camellia.Direction) : specDir (ofSpecDir d) = d := by cases d <;> rfl

/-- The direction `vg_camellia_prepare_keys`'s `decrypt` selects. -/
def dirOf (decrypt : BitVec 64) : Dir := if decrypt = 0 then .encrypt else .decrypt

theorem specDir_dirOf (decrypt : BitVec 64) :
    specDir (dirOf decrypt) = Proof.Camellia.Prepared.directionOf decrypt.toNat := by
  unfold dirOf Proof.Camellia.Prepared.directionOf
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
  congr 2; omega_arith

theorem layout_table (R : Nat) : layout.table R = [(384, 40), (768, 64 * (8 * (R / 6) + 2))] := rfl
theorem evenSlot_eq : evenSlot = 48 := rfl
theorem m3Slot_eq : m3Slot = 52 := rfl

theorem table_ranges (R o : Nat) :
    (∃ r ∈ layout.table R, ∃ i < r.2, o = r.1 + i) ↔
      (evenSlot ≤ o / 8 ∧ o / 8 ≤ m3Slot) ∨ (keySlot ≤ o / 8 ∧ o / 8 < keySlot + 8 * (8 * (R / 6) + 2)) := by
  rw [layout_table, evenSlot_eq, m3Slot_eq, keySlot_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨r, hr | hr, i, hi, rfl⟩ <;> subst hr <;> dsimp only at hi ⊢ <;> omega_arith
  · intro h
    rcases h with h | h
    · exact ⟨_, .inl rfl, o - 384, by dsimp only; omega_arith, by dsimp only; omega_arith⟩
    · exact ⟨_, .inr rfl, o - 768, by dsimp only; omega_arith, by dsimp only; omega_arith⟩

theorem holds_of_words {R : Nat} {m : Mem} {B : Addr} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (h : TableWordsAt R m B w (ofSpecDir d)) : Proof.Camellia.Prepared.Holds layout m B R w d := by
  intro r hr i hi
  have hw := (table_ranges R (r.1 + i)).1 ⟨r, hr, i, hi, rfl⟩
  rw [word_byte_addr, byte_of_readW m _ (by omega_arith), h _ hw]
  rfl

theorem words_of_holds {R : Nat} {m : Mem} {B : Addr} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (h : Proof.Camellia.Prepared.Holds layout m B R w d) : TableWordsAt R m B w (ofSpecDir d) := by
  intro k hk
  simp only [Mem.readW, BitVec.setWidth_eq]
  refine Mem.read_eq_of_bytes fun j hj => ?_
  obtain ⟨r, hr, i, hi, ho⟩ := (table_ranges R (8 * k + j)).2 (by
    rw [show (8 * k + j) / 8 = k by omega_arith]; exact hk)
  have := h r hr i hi
  rw [← ho, word_byte_addr, show (8 * k + j) / 8 = k by omega_arith, show (8 * k + j) % 8 = j by omega_arith] at this
  rw [this]
  show (preparedWord R w (ofSpecDir d) ((8 * k + j) / 8)).extractLsb' (8 * ((8 * k + j) % 8)) 8 = _
  rw [show (8 * k + j) / 8 = k by omega_arith, show (8 * k + j) % 8 = j by omega_arith]

theorem entryW_eq (m : Mem) (B : Addr) (e j : Nat) :
    entryW m B e j = m.readW (wordAddr B (keySlot + 8 * e + j)) 64 := by
  rw [entryW, wordAddr, show 8 * (keySlot + 8 * e + j) = 8 * keySlot + 64 * e + 8 * j by omega_arith]

theorem preparedWord_entry (R : Nat) (w : List (BitVec 64)) (d : Dir) {e j : Nat} (hj : j < 8) :
    preparedWord R w d (keySlot + 8 * e + j) = keyPlane (keyEntry w (R / 6) d e) j := by
  have hc : ¬ (keySlot + 8 * e + j < keySlot) := by omega_arith
  simp only [preparedWord, hc, ↓reduceIte]
  rw [show (keySlot + 8 * e + j - keySlot) / 8 = e by omega_arith, show (keySlot + 8 * e + j - keySlot) % 8 = j by omega_arith]

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
  rw [entryW_eq, h _ (.inr (by omega_arith)), preparedWord_entry R w d hj]

theorem words_of_readyAt {R : Nat} {m : Mem} {B : Addr} {w : List (BitVec 64)} {d : Dir}
    (h : ReadyAt d R m B w) : TableWordsAt R m B w d := by
  intro k hk
  rcases hk with hk | hk
  · have hkv : ∃ kv ∈ layerMasks, kv.1 = k := by
      rw [evenSlot_eq, m3Slot_eq] at hk
      simp only [layerMasks, List.mem_cons, List.not_mem_nil, or_false]
      rcases (by omega_arith : k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52) with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, .inl rfl, rfl⟩
      · exact ⟨_, .inr (.inl rfl), rfl⟩
      · exact ⟨_, .inr (.inr (.inl rfl)), rfl⟩
      · exact ⟨_, .inr (.inr (.inr (.inl rfl))), rfl⟩
      · exact ⟨_, .inr (.inr (.inr (.inr rfl))), rfl⟩
    obtain ⟨kv, hkv, rfl⟩ := hkv
    rw [h.1 kv hkv, preparedWord_mask R w d hkv]
  · obtain ⟨e, j, hj, rfl⟩ : ∃ e j, j < 8 ∧ k = keySlot + 8 * e + j :=
      ⟨(k - keySlot) / 8, (k - keySlot) % 8, by omega_arith, by omega_arith⟩
    have he : e < 8 * (R / 6) + 2 := by omega_arith
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
        (Proof.Camellia.Prepared.wordsAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat) (dirOf (s₀.gpr .x2)) := by
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
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega_arith
  have hz : isa.eval (.zero .x t0) s₁ = some (decide (g = 3)) := (eval_zero s₁ t0).trans (by
    rw [hz₁]; exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩))
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
    exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [endSlot_eq, savedSlot_eq]; omega_arith)
      (by rw [savedSlot_eq]; omega_arith)
  obtain ⟨s₃, e₃, rg₃, -, m₃, -, -⟩ := restore_ok (by rw [k₂.wr, wr₁]; exact hwS) base₂ sv₂
  refine WP.of_runBlock ⟨s₃, e₃, rg₃, ?_⟩
  rw [m₃]
  refine words_of_readyAt ⟨k₂.masks.at base₂, fun i hi => ?_⟩
  rw [hgR] at hi ⊢
  have := k₂.ent i hi
  have hp : permOf (dirOf (s₀.gpr .x2)) g i < 8 * g + 2 := dirPerm_lt _ hi
  have hl : permOf (dirOf (s₀.gpr .x2)) g i < Spec.Camellia.scheduleLength R := by
    simp only [Spec.Camellia.scheduleLength]; omega_arith
  rw [keyEntry_eq]
  show EntryOk s₂.mem b i ((Proof.Camellia.schedWords s₀.mem sched R).getD _ 0)
  rw [schedWords_getD _ _ hl]
  rw [wordAt_frame f₁ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dSS.sub_left (VG.Offset.sub_base sched (by simp only [Spec.Camellia.scheduleLength] at hl; omega_arith))).sub_right
        (Region.sub_prefix (by rw [keySlot_eq, slots_eq]; omega_arith))
    · exact (dSS.sub_left (VG.Offset.sub_base sched (by simp only [Spec.Camellia.scheduleLength] at hl; omega_arith))).sub_right
        (VG.Offset.sub_base b (by rw [savedSlot_eq, slots_eq]; omega_arith))] at this
  exact this

/-- The entry of the postwhitening subkey, for `g` groups. -/
theorem endAddr_ok (s : State) {g : Nat} (hg : g = 3 ∨ g = 4) :
    ∃ s', runBlock isa (endAddr g) s = some s' ∧
      s'.gpr .x4 = s.gpr sb + BitVec.ofNat 64 (8 * keySlot + 512 * g) ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .x4 sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ .x4 .x4 (imm := 8 * keySlot + 512 * g)
    (by rw [keySlot_eq]; omega_arith)
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
  have hg : g = 3 ∨ g = 4 := by omega_arith
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .x1
  have b₁ : s₁.gpr sb = b := r₁.trans hb
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁]; exact hwr) b₁
  obtain ⟨s₃, e₃, t₃, o₃, m₃, rd₃, wr₃⟩ := subI_ok s₂ t0 .x0 (imm := 18) (by decide)
  have b₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), g₂, b₁]
  have hz₃ : isa.eval (.zero .x t0) s₃ = some (decide (g = 3)) := by
    rw [eval_zero, t₃, g₂, o₁ _ (by decide),
      show s₀.gpr .x0 = BitVec.ofNat 64 R by simp only [R, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩)
  have hfit := fitB
  rw [slots_eq] at hfit
  have slot₃ : ∀ k < savedSlot, s₃.mem.readW (wordAddr b k) 64 = s₀.mem.readW (wordAddr b k) 64 := fun k hk => by
    rw [m₃, ← m₁]
    refine f₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint b (.inl (by rw [savedSlot_eq] at hk ⊢; omega_arith)) (by rw [savedSlot_eq] at hk; omega_arith)
      (by rw [savedSlot_eq]; omega_arith)
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃], ?_⟩)
  -- The postwhitening's entry.
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => s₄.gpr .x4 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) ∧
      (∀ r, r ≠ .x4 → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr)
    (WP.ite (decide (g = 3)) hz₃ (fun h => ?_) (fun h => ?_)) fun s₄ ⟨x4₄, o₄, m₄, rd₄, wr₄⟩ => ?_)
  · have hg3 : g = 3 := of_decide_eq_true h
    obtain ⟨s', e', x4', o', m', rd', wr'⟩ := endAddr_ok s₃ (g := 3) (.inl rfl)
    exact WP.of_runBlock ⟨s', e', by rw [x4', b₃, hg3], o', m', rd', wr'⟩
  · have hg4 : g = 4 := by have := of_decide_eq_false h; omega_arith
    obtain ⟨s', e', x4', o', m', rd', wr'⟩ := endAddr_ok s₃ (g := 4) (.inr rfl)
    exact WP.of_runBlock ⟨s', e', by rw [x4', b₃, hg4], o', m', rd', wr'⟩
  have b₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), b₃]
  have hcore : CorePre s₄ g (keyEntry w g d) :=
    { scr := by rw [b₄, wr₄, wr₃, wr₂, wr₁]; exact hwr
      fit := by rw [b₄]; exact fitB
      nk34 := by omega_arith
      masks := fun kv hkv => by
        show s₄.mem.readW (wordAddr (s₄.gpr sb) kv.1) 64 = kv.2
        rw [b₄, m₄, slot₃ _ (by have := mask_in hkv; rw [m3Slot_eq] at this; rw [savedSlot_eq]; omega_arith)]
        exact hr.1 kv hkv
      keys := fun i hi => by
        have := hr.2 i (by rw [hgR]; exact hi)
        rw [hgR] at this
        refine this.congr fun j hj => ?_
        rw [b₄, entryW_eq, entryW_eq, m₄, slot₃ _ (by rw [keySlot_eq, savedSlot_eq]; omega_arith)]
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
    · exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by rw [keySlot_eq, savedSlot_eq]; omega_arith)
        (by rw [savedSlot_eq]; omega_arith)
    · exact VG.Offset.disjoint b (.inl (by rw [savedSlot_eq, tailSlot_eq]; omega_arith)) (by rw [savedSlot_eq]; omega_arith)
        (by rw [tailSlot_eq]; omega_arith)
  obtain ⟨s₆, e₆, rg₆, -, m₆, rd₆, wr₆⟩ := restore_ok (by rw [c₅.wr, wr₄, wr₃, wr₂, wr₁]; exact hwr) base₅ sv₅
  have hk5 : ∀ k, keySlot ≤ k → k < savedSlot →
      s₅.mem.readW (wordAddr b k) 64 = s₀.mem.readW (wordAddr b k) 64 := fun k h1 h2 => by
    rw [← slot₃ k h2, ← m₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by omega_arith) (by rw [savedSlot_eq] at h2; omega_arith)
    · exact VG.Offset.disjoint b (.inl (by rw [savedSlot_eq, tailSlot_eq] at *; omega_arith))
        (by rw [savedSlot_eq] at h2; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  refine WP.of_runBlock ⟨s₆, e₆, fun i hi => by rw [rg₆ i hi, o₁ _ (sreg_ne i hi)], ?_, ?_,
    by rw [rd₆, c₅.rd, rd₄, rd₃, rd₂, rd₁], by rw [wr₆, c₅.wr, wr₄, wr₃, wr₂, wr₁], fun j hj => ?_⟩
  · refine ⟨fun kv hkv => by rw [m₆]; exact c₅.masks.at base₅ kv hkv, fun i hi => (hr.2 i hi).congr fun j hj => ?_⟩
    have hg4 : (s₀.gpr .x0).toNat / 6 ≤ 4 := by omega_arith
    rw [entryW_eq, entryW_eq, m₆, hk5 _ (by omega_arith) (by rw [keySlot_eq, savedSlot_eq]; omega_arith)]
  · rw [m₆]
    have l₄ : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * savedSlot), 208⟩] s₀.mem s₄.mem := by
      rw [m₄, m₃, ← m₁]
      exact f₂.sub fun r hr => ⟨⟨b + BitVec.ofNat 64 (8 * savedSlot), 208⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub b (d := 8 * savedSlot) (n := 80) (e := 8 * savedSlot) (k := 208) (by omega_arith) (by omega_arith)⟩
    exact l₄.trans (f₅.sub fun r hr => by
      simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
          VG.Offset.sub b (by rw [savedSlot_eq, tailSlot_eq] <;> omega_arith) (by rw [savedSlot_eq, tailSlot_eq] <;> omega_arith)⟩)
  · have := o₅ j hj
    simp only [blk, base₅, b₄] at this
    rw [m₆, this, ← hgR, crypt_spec d hR, m₄, m₃]
    refine congrArg _ (Vector.ext fun i hi => ?_)
    simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn]
    rw [show b + BitVec.ofNat 64 (8 * tailSlot + 16 * j) + BitVec.ofNat 64 i =
      b + BitVec.ofNat 64 (8 * tailSlot) + BitVec.ofNat 64 (16 * j + i) by
        rw [VG.Offset.add_add, VG.Offset.add_add]; congr 2; omega_arith, ← m₁]
    refine f₂.bytes (R := ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩) (fun r hr => ?_) (by show (128 : Nat) ≤ 2 ^ 64; decide)
      (by show 16 * j + i < 128; omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨b + BitVec.ofNat 64 (8 * savedSlot), 80⟩
    exact VG.Offset.disjoint b (.inr (by rw [savedSlot_eq, tailSlot_eq] <;> omega_arith)) (by rw [tailSlot_eq] <;> omega_arith)
      (by rw [savedSlot_eq]; omega_arith)

end VG.Proof.Camellia.AArch64

end

end

/-!
# Camellia's prepared subkeys and batches on AArch64 meet their contracts

`prep_correct` and `crypt_correct`: `vg_camellia_prepare_keys` and
`vg_camellia_crypt_prepared` against `Proof.Camellia.Prepared`, with
`layout`. Each body runs from the state narrowed to ECB's scratch buffer
(`prepareBody_wp`, `cryptBody_wp`) and then from the whole working space
(`Exec.widen`), which it changes only where the narrowed run may. A batch's
blocks are ECB in the direction and under the subkeys of any words whose
table its working space holds: the run from it is the run from the table
the precondition gives (`Exec.det`).
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Camellia.AArch64
open VG.Proof.Camellia (blockFn)
open VG.Proof.Camellia.Prepared (Holds Keeps)

/-! ## Narrowing the working space -/

/-- `s` with its writable region the first `8 * slots` bytes of `ws`. -/
abbrev narrow (s : State) (ws : Addr) : State := s.withRegions s.rd [⟨ws, 8 * slots⟩]

theorem narrow_covers (s : State) {ws : Addr} {len : Nat} (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * slots ≤ len) :
    Covers ((narrow s ws).rd ++ (narrow s ws).wr) (s.rd ++ s.wr) ∧ Covers (narrow s ws).wr s.wr := by
  have h : Covers [⟨ws, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨ws, len⟩, by rw [hw]; simp, 0, by rw [BitVec.add_zero], by show 0 + 8 * slots ≤ len; omega_using [hl]⟩
  exact ⟨Covers.append (Covers.refl _) h, h⟩

/-- A run from the narrowed state is a run from `s`, to the state with `s`'s regions. -/
theorem exec_widen {c : Prog isa} {s s' : State} {t : List Leak} {ws : Addr} {len : Nat}
    (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * slots ≤ len) (h : Exec isa c (narrow s ws) t s') :
    Exec isa c s t (s'.withRegions s.rd s.wr) := by
  have := Exec.widen h (narrow_covers s hw hl).1 (narrow_covers s hw hl).2
  rwa [State.withRegions_withRegions, State.withRegions_self] at this

/-- The bytes of `ws` from `8 * slots` on keep their values. -/
theorem keeps_of_frame {m m' : Mem} {ws : Addr} {wsLen : Nat} {rs : List (Nat × Nat)}
    (hf : Frame [⟨ws, 8 * slots⟩] m m') (fit : ws.toNat + wsLen * 8 ≤ 2 ^ 64)
    (hrs : ∀ i, (∀ r ∈ rs, i < r.1 ∨ r.1 + r.2 ≤ i) → 8 * slots ≤ i) :
    Keeps ws wsLen rs m m' := fun i hi hout =>
  hf _ fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains] at hc
    rw [Mem.sub_ofNat_toNat ws (by omega_using [fit, hi])] at hc
    have := hrs i hout
    omega_using [hc, this]

theorem size_eq : layout.size = 8 * slots := rfl

/-- The callee-saved registers, from those the bodies restore and `x30`. -/
theorem helperAbi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hv : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (h₁ : ∀ i < 10, s'.gpr (sreg i) = s.gpr (sreg i)) (h₃ : s'.gpr .x30 = s.gpr .x30) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, hv⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_using [])
  · exact h₁ 1 (by omega_using [])
  · exact h₁ 2 (by omega_using [])
  · exact h₁ 3 (by omega_using [])
  · exact h₁ 4 (by omega_using [])
  · exact h₁ 5 (by omega_using [])
  · exact h₁ 6 (by omega_using [])
  · exact h₁ 7 (by omega_using [])
  · exact h₁ 8 (by omega_using [])
  · exact h₁ 9 (by omega_using [])
  · exact h₃

/-! ## The preparation -/

/-- `vg_camellia_prepare_keys` on AArch64. -/
def prepAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 272⟩
    let ws : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩
    s.rd = [sched] ∧ s.wr = [ws] ∧ sched.Disjoint ws ∧ (s.gpr .x0).toNat + 272 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + (s.gpr .x4).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 18 ∨ (s.gpr .x1).toNat = 24) ∧ (s.gpr .x2).toNat ≤ 1 ∧
      layout.size ≤ 8 * (s.gpr .x4).toNat
  post s s' :=
    Holds layout s'.mem (s.gpr .x3) (s.gpr .x1).toNat
        (Proof.Camellia.Prepared.wordsAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Proof.Camellia.Prepared.directionOf (s.gpr .x2).toNat) ∧
      Keeps (s.gpr .x3) (s.gpr .x4).toNat layout.prepScratch s.mem s'.mem
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

theorem prep_correct (s : State) (hs : prepAArch64.pre s) :
    ∃ t s', Exec isa prepareKeys s t s' ∧ abiPreserved s s' ∧ prepAArch64.post s s' := by
  obtain ⟨hrd, hwr, dSS, fitK, fitW, hR, -, hsz⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .x4).toNat * 8 := by omega_using [hsz]
  have w := prepareBody_wp (s₀ := narrow s (s.gpr .x3)) hrd rfl
    (dSS.sub_right (Region.sub_prefix hl)) fitK (by show (s.gpr .x3).toNat + 8 * slots ≤ 2 ^ 64; omega_using [fitW, hsz]) hR
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) w (by lit_decide) (by lit_decide)
  have f := (Exec.regions he (by lit_decide)).2.2.2
  have he' := exec_widen hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he',
    helperAbi_of he' (Exec.preservedV he' (by lit_decide)) h₁ (h₃ _ (by simp)), ?_, keeps_of_frame f fitW fun i hi => ?_⟩
  · refine holds_of_words ?_
    rw [← specDir_dirOf, ofSpecDir_specDir]
    exact h₂
  · have := hi _ (List.mem_singleton_self _)
    simp only at this
    omega_using [this]

/-! ## A batch -/

/-- `vg_camellia_crypt_prepared` on AArch64. -/
def cryptAArch64 : Contract AArch64.isa where
  pre s :=
    let ws : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .x0).toNat = 18 ∨ (s.gpr .x0).toNat = 24) ∧ layout.size ≤ 8 * (s.gpr .x2).toNat ∧
      ∃ w d, Holds layout s.mem (s.gpr .x1) (s.gpr .x0).toNat w d
  post s s' :=
    (∀ w d, Holds layout s.mem (s.gpr .x1) (s.gpr .x0).toNat w d →
      Spec.Camellia.blocksAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords (s.gpr .x0).toNat w) d
          (Spec.Camellia.blocksAt s.mem (s.gpr .x1 + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (s.gpr .x1) (s.gpr .x2).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

theorem blocks_of (B : Addr) {m m' : Mem} {k : Spec.Camellia.Subkeys} {d : Spec.Camellia.Direction}
    (h : ∀ j < 8, Spec.Camellia.blockAt m' (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        blockFn k d (Spec.Camellia.blockAt m (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)))) :
    Spec.Camellia.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Camellia.ecb k d (Spec.Camellia.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Camellia.ecb_eq]
  simp only [Spec.Camellia.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hj
  simp only [Function.comp_apply, VG.Offset.add_add]
  exact h j hj

/-- The masks' bytes, the same in two working spaces holding tables. -/
theorem mask_byte {R : Nat} {m m' : Mem} {B : Addr} {w w' : List (BitVec 64)} {d d' : Dir}
    (h : TableWordsAt R m B w d) (h' : TableWordsAt R m' B w' d') {i : Nat} (hi : 8 * evenSlot ≤ i ∧ i < 8 * (m3Slot + 1)) :
    m' (B + BitVec.ofNat 64 i) = m (B + BitVec.ofNat 64 i) := by
  have hw : (evenSlot ≤ i / 8 ∧ i / 8 ≤ m3Slot) ∨ (keySlot ≤ i / 8 ∧ i / 8 < keySlot + 8 * (8 * (R / 6) + 2)) :=
    .inl (by omega_using [hi])
  rw [word_byte_addr, byte_of_readW m' (wordAddr B (i / 8)) (j := i % 8) (by omega_using []),
    byte_of_readW m (wordAddr B (i / 8)) (j := i % 8) (by omega_using []), h _ hw, h' _ hw]
  have hm : ∀ (w : List (BitVec 64)) (d : Dir), preparedWord R w d (i / 8) =
      (layerMasks.find? (·.1 = i / 8)).elim 0 (·.2) := fun _ _ => by
    have hc : i / 8 < keySlot := by rw [keySlot_eq]; rw [m3Slot_eq] at hi; omega_using [hi]
    simp only [preparedWord, hc, ↓reduceIte]
  rw [hm, hm]

theorem crypt_correct (s : State) (hs : cryptAArch64.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptAArch64.post s s' := by
  obtain ⟨-, hwr, fitW, hR, hsz, w₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .x2).toNat * 8 := by omega_using [hsz]
  have hwN : (⟨(narrow s (s.gpr .x1)).gpr .x1, 8 * slots⟩ : Region) ∈ (narrow s (s.gpr .x1)).wr := by simp
  have fitN : ((narrow s (s.gpr .x1)).gpr .x1).toNat + 8 * slots ≤ 2 ^ 64 := by
    show (s.gpr .x1).toNat + 8 * slots ≤ 2 ^ 64; omega_using [fitW, hsz]
  obtain ⟨t, s', he, ⟨h₁, hRd, hF, -, -, -⟩, h₃⟩ := WP.gprs (rs := [.x30])
    (cryptBody_wp hwN fitN hR (readyAt_of_words (words_of_holds hH))) (by lit_decide) (by lit_decide)
  have he' := exec_widen hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', helperAbi_of he' (Exec.preservedV he' (by lit_decide)) h₁ (h₃ _ (by simp)),
    fun w d hk => ?_, fun i hi hout => ?_⟩
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, hB₂⟩ := cryptBody_wp hwN fitN hR (readyAt_of_words (words_of_holds hk))
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    refine blocks_of _ fun j hj => ?_
    have := hB₂ j hj
    rw [specDir_ofSpecDir] at this
    exact this
  · have hfit := fitW
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [evenSlot_eq, m3Slot_eq, keySlot_eq, savedSlot_eq, tailSlot_eq] at hout
    by_cases hm : 384 ≤ i ∧ i < 424
    · exact mask_byte (words_of_holds hH) (words_of_readyAt hRd) (by rw [evenSlot_eq, m3Slot_eq]; omega_using [hm])
    · refine hF _ fun r hr hc => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [Region.Contains, narrow, State.withRegions_gpr] at hc
      · rw [Mem.sub_ofNat_toNat _ (by omega_using [fitW, hi]), keySlot_eq] at hc; omega_using [hout, hm, hc]
      · rw [VG.Offset.sub_toNat' _ (by rw [savedSlot_eq]; omega_using []) (by omega_using [fitW, hi]), savedSlot_eq] at hc
        split at hc <;> omega_arith

end VG.Proof.Camellia.AArch64

end

end

/-!
# Camellia's core for the modes on AArch64

`dirCoreSpec d`: Camellia's core for the direction `d`
(`Impl.Camellia.AArch64.dirCore d`) meets what the modes need of a core
(`Proof.Modes.AArch64.CoreSpec`), with the key the number of rounds and the
schedule's words, its cipher `Spec.Camellia.cipher` under them for
encryption and `Spec.Camellia.invCipher` for decryption, and the key ready
when the masks and the table of subkeys in `d`'s order are in the scratch
buffer (`ReadyAt`) and `x4` holds the number of rounds (which the modes do
not write). `modeCoreSpec` is encryption's, for CTR.

`prepare` and `crypt` call `vg_camellia_prepare_keys` and
`vg_camellia_crypt_prepared` (`WP.call`, with their contracts on AArch64,
`prepAArch64` and `cryptAArch64`) on the core's slots; around each call,
`v26`–`v30` keep `x4`, `sb`, the return address and the two registers the
modes keep for the core, since neither function writes a vector register.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (sb t0 kp movR)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion bufAddr Layout CoreSpec modeRegs dup_ok umov_ok
  extract_ofVDwords vSafe keepsV_of_vSafe runBlock_app)
open VG.Proof.Camellia (schedWords schedWords_getD wordAt_frame bytesAt_eq_blockAt ofFn_toList blockFn)
open VG.Proof.Camellia.Prepared (Holds Keeps)

/-- The number of rounds in `x1` and the schedule at `x0`, outside the
regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  ∃ p : Addr, s.gpr .x0 = p ∧ s.gpr .x1 = BitVec.ofNat 64 k.1 ∧ (k.1 = 18 ∨ k.1 = 24) ∧
    k.2 = schedWords s.mem p k.1 ∧ (⟨p, 272⟩ : Region) ∈ s.rd ∧ p.toNat + 272 ≤ 2 ^ 64 ∧
    ∀ r ∈ rs, Region.Disjoint ⟨p, 272⟩ r

/-- The table of the subkeys of `k`'s rounds and words in the order of `d`,
and the number of rounds in `x4`. -/
def Ready (d : Dir) (s : State) (B : Addr) (k : Nat × List (BitVec 64)) : Prop :=
  (k.1 = 18 ∨ k.1 = 24) ∧ ReadyAt d k.1 s.mem B k.2 ∧ s.gpr .x4 = BitVec.ofNat 64 k.1

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ layerMasks) : 48 ≤ kv.1 ∧ kv.1 < 53 := by
  simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
    simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]

theorem total_eq (d : Dir) : (dirCore d).total = slots + 12 := rfl

/-- A word of the core's slots outside the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {dir : Dir} {B : Addr} {d : Nat} (hd : d + 8 ≤ 8 * tailSlot) {r : Region}
    (hr : Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B (show d + 8 ≤ 8 * slots by rw [slots_eq]; rw [tailSlot_eq] at hd; omega_arith))
  · refine Region.Disjoint.sub_right ?_ h
    show Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ ⟨B + BitVec.ofNat 64 (8 * tailSlot), 128⟩
    exact VG.Offset.disjoint B (by simp only [tailSlot_eq] at hd ⊢; omega_arith)
      (by simp only [tailSlot_eq] at hd; omega_arith) (by simp only [tailSlot_eq]; omega_arith)

theorem ready_frame {dir : Dir} {s s' : State} {B : Addr} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready dir s B k) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B))
    (_ : Modes.AArch64.WrIn rs s s') (hg : ∀ r, r ∉ modeRegs (dirCore dir) → s'.gpr r = s.gpr r) :
    Ready dir s' B k := by
  obtain ⟨hR, ⟨hm, he⟩, hx4⟩ := h
  obtain hR' : ∀ d, d + 8 ≤ 8 * tailSlot →
      s'.mem.readW (B + BitVec.ofNat 64 d) 64 = s.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint h1 (hd r hr)) (by decide)
  obtain hg4 : k.1 / 6 ≤ 4 := by omega_arith
  refine ⟨hR, ⟨fun kv hkv => ?_, fun i hi => (he i hi).congr fun j hj => ?_⟩, ?_⟩
  · have hk := mask_range hkv
    rw [← hm kv hkv]
    exact hR' (8 * kv.1) (by rw [tailSlot_eq]; omega_arith)
  · exact hR' (8 * keySlot + 64 * i + 8 * j) (by rw [keySlot_eq, tailSlot_eq]; omega_arith)
  · rw [hg .x4 (by cases dir <;> decide), hx4]

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.x0, .x1], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hx1, hR, hws, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .x0 List.mem_cons_self, hp], by rw [hr .x1 (List.mem_cons_of_mem _ List.mem_cons_self), hx1],
    hR, ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hws]
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  obtain hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega_arith
  exact (wordAt_frame hf fun r hr => (hdis r hr).sub_left (VG.Offset.sub_base p hl)).symm

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Camellia.Subkeys → Spec.Cbc.Cipher
  | .encrypt => Spec.Camellia.cipher
  | .decrypt => Spec.Camellia.invCipher

/-- The cipher on a block in memory: its block function. -/
theorem dirCipher_bytes (d : Dir) (K : Spec.Camellia.Subkeys) (m : Mem) (p : Addr) :
    dirCipher d K (Spec.Aes.bytesAt m p 16) = (blockFn K (specDir d) (Spec.Camellia.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Camellia.cipher, bytesAt_eq_blockAt, ofFn_toList]; rfl
  · rw [dirCipher, Spec.Camellia.invCipher, bytesAt_eq_blockAt, ofFn_toList]; rfl

/-! ## Around the calls -/

/-- The state after `keepHeadWith r`. -/
def kept (r : Reg) (s : State) : State :=
  ((((s.setV .v28 (ofVDwords (s.gpr .x30) (s.gpr .x30))).setV .v27 (ofVDwords (s.gpr sb) (s.gpr sb))).setV
    .v29 (ofVDwords (s.gpr .x23) (s.gpr .x23))).setV .v30 (ofVDwords (s.gpr .x24) (s.gpr .x24))).setV
    .v26 (ofVDwords (s.gpr r) (s.gpr r))

theorem kept_mem (r : Reg) (s : State) : (kept r s).mem = s.mem := by
  simp only [kept, RegUpd.mem_setV]

theorem kept_rd (r : Reg) (s : State) : (kept r s).rd = s.rd := by
  simp only [kept, RegUpd.rd_setV]

theorem kept_wr (r : Reg) (s : State) : (kept r s).wr = s.wr := by
  simp only [kept, RegUpd.wr_setV]

theorem keepHead_ok (r : Reg) (s : State) : runBlock isa (keepHeadWith r) s = some (kept r s) := by
  rw [show keepHeadWith r = [.vop (.dup .d2 .v28 .x30)] ++ ([.vop (.dup .d2 .v27 sb)] ++
      ([.vop (.dup .d2 .v29 .x23)] ++ ([.vop (.dup .d2 .v30 .x24)] ++ [.vop (.dup .d2 .v26 r)]))) from rfl,
    runBlock_app, dup_ok, Option.bind_some, runBlock_app, dup_ok, Option.bind_some, runBlock_app, dup_ok,
    Option.bind_some, runBlock_app, dup_ok, Option.bind_some, dup_ok]
  rfl

/-- The vector registers that keep the five. -/
abbrev keepVs : List VReg := [.v26, .v27, .v28, .v29, .v30]

theorem keepTail_ok (s : State) : ∃ s', runBlock isa keepTail s = some s' ∧
    s'.gpr sb = (s.v .v27).extractLsb' 0 64 ∧ s'.gpr .x30 = (s.v .v28).extractLsb' 0 64 ∧
    s'.gpr .x23 = (s.v .v29).extractLsb' 0 64 ∧ s'.gpr .x24 = (s.v .v30).extractLsb' 0 64 ∧
    s'.gpr .x4 = (s.v .v26).extractLsb' 0 64 ∧
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x sb ((s.v .v27).extractLsb' 0 64)
  let s₂ := s₁.write .x .x30 ((s₁.v .v28).extractLsb' 0 64)
  let s₃ := s₂.write .x .x23 ((s₂.v .v29).extractLsb' 0 64)
  let s₄ := s₃.write .x .x24 ((s₃.v .v30).extractLsb' 0 64)
  let s₅ := s₄.write .x .x4 ((s₄.v .v26).extractLsb' 0 64)
  refine ⟨s₅, by
    rw [show keepTail = [.umov .x sb .v27 0] ++ ([.umov .x .x30 .v28 0] ++ ([.umov .x .x23 .v29 0] ++
      ([.umov .x .x24 .v30 0] ++ [.umov .x .x4 .v26 0]))) from rfl, runBlock_app, umov_ok, Option.bind_some,
      runBlock_app, umov_ok, Option.bind_some, runBlock_app, umov_ok, Option.bind_some, runBlock_app, umov_ok,
      Option.bind_some, umov_ok], ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [(Modes.AArch64.write_ok _ .x4 _).2.1 sb (by decide), (Modes.AArch64.write_ok _ .x24 _).2.1 sb (by decide),
      (Modes.AArch64.write_ok _ .x23 _).2.1 sb (by decide), (Modes.AArch64.write_ok _ .x30 _).2.1 sb (by decide),
      (Modes.AArch64.write_ok _ sb _).1]
  · rw [(Modes.AArch64.write_ok _ .x4 _).2.1 .x30 (by decide), (Modes.AArch64.write_ok _ .x24 _).2.1 .x30 (by decide),
      (Modes.AArch64.write_ok _ .x23 _).2.1 .x30 (by decide), (Modes.AArch64.write_ok _ .x30 _).1]; rfl
  · rw [(Modes.AArch64.write_ok _ .x4 _).2.1 .x23 (by decide), (Modes.AArch64.write_ok _ .x24 _).2.1 .x23 (by decide),
      (Modes.AArch64.write_ok _ .x23 _).1]; rfl
  · rw [(Modes.AArch64.write_ok _ .x4 _).2.1 .x24 (by decide), (Modes.AArch64.write_ok _ .x24 _).1]; rfl
  · rw [(Modes.AArch64.write_ok _ .x4 _).1]; rfl

/-- A block that writes no vector register `v` keeps it. -/
theorem runBlock_keepV {is : List Instr} {s s' : State} {v : VReg} (hv : ∀ i ∈ is, vdstOf i ≠ some v)
    (e : runBlock isa is s = some s') : s'.v v = s.v v := by
  obtain w : WP isa (.block is) s fun x => x = s' := WP.of_runBlock ⟨s', e, rfl⟩
  obtain ⟨t, u, he, rfl⟩ := w
  exact Exec.vec (c := .block is) hv he

/-- The five registers back, from a state whose `v26`–`v30` are `kept r s`'s. -/
theorem keepTail_kept {r : Reg} {s s₁ : State} (hv : ∀ v ∈ keepVs, s₁.v v = (kept r s).v v) :
    ∃ s', runBlock isa keepTail s₁ = some s' ∧ s'.gpr sb = s.gpr sb ∧ s'.gpr .x30 = s.gpr .x30 ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ s'.gpr .x4 = s.gpr r ∧
      s'.mem = s₁.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr := by
  obtain ⟨s', e', r27, r28, r29, r30, r26, m', rd', wr'⟩ := keepTail_ok s₁
  refine ⟨s', e', ?_, ?_, ?_, ?_, ?_, m', rd', wr'⟩
  · rw [r27, hv .v27 (by simp)]; exact extract_ofVDwords _
  · rw [r28, hv .v28 (by simp)]; exact extract_ofVDwords _
  · rw [r29, hv .v29 (by simp)]; exact extract_ofVDwords _
  · rw [r30, hv .v30 (by simp)]; exact extract_ofVDwords _
  · rw [r26, hv .v26 (by simp)]; exact extract_ofVDwords _

/-- Code that writes none of `v26`–`v30`. -/
def keepsVs (c : Prog isa) : Bool :=
  vSafe .v26 c && vSafe .v27 c && vSafe .v28 c && vSafe .v29 c && vSafe .v30 c

theorem prepareKeys_vsafe : keepsVs prepareKeys = true := by
  unfold keepsVs; lit_decide

theorem cryptPrepared_vsafe : keepsVs cryptPrepared = true := by
  unfold keepsVs; lit_decide

/-- A call of code that keeps `v26`–`v30` keeps them. -/
theorem call_keepsV {name : String} {c : Prog isa} (hc : keepsVs c = true)
    {s s' : State} {t : List Leak} (he : Exec isa (.call name c) s t s') :
    ∀ v ∈ keepVs, s'.v v = s.v v := fun v hv => by
  simp only [keepsVs, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h26, h27⟩, h28⟩, h29⟩, h30⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact keepsV_of_vSafe (c := .call name c) h26 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) h27 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) h28 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) h29 _ _ _ he
  · exact keepsV_of_vSafe (c := .call name c) h30 _ _ _ he

theorem toNat_slots : (BitVec.ofNat 64 slots).toNat = slots := by rw [BitVec.toNat_ofNat, slots_eq]

/-- The core's slots, as the calls' working space. -/
theorem ws_covers {s : State} {B : Addr} {d : Dir} (hs : ScrIn s B (dirCore d).total) :
    Covers [⟨B, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, hs.wr, 0, by rw [BitVec.add_zero], by show 0 + 8 * slots ≤ 8 * (dirCore d).total; rw [total_eq]; omega_arith⟩

theorem toNat_rounds {R : Nat} (hR : R = 18 ∨ R = 24) : (BitVec.ofNat 64 R).toNat = R := by
  rcases hR with rfl | rfl <;> rfl

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready d s' B k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hp, hx1, hRr, hws, hin, hfit, hdis⟩ := hk
  simp only at hx1 hRr hws
  have hfB := hs.fit
  rw [total_eq] at hfB
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movz_ok (kept .x1 s) .x2 (v := dirFlagOf d)
    (by cases d <;> decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .x3 sb
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := Modes.AArch64.movz_ok s₃ .x4 (v := slots) (by decide)
  obtain eargs : runBlock isa ([.movz .x .x2 (BitVec.ofNat 16 (dirFlagOf d)) 0] ++ ([movR .x3 sb] ++
      [.movz .x .x4 (BitVec.ofNat 16 slots) 0])) (kept .x1 s) = some s₄ := by
    rw [runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  obtain v₄ : ∀ v ∈ keepVs, s₄.v v = (kept .x1 s).v v := fun v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> cases d <;> exact runBlock_keepV (by decide) eargs
  obtain x0₄ : s₄.gpr .x0 = p := by
    rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide)]; exact hp
  obtain x1₄ : s₄.gpr .x1 = BitVec.ofNat 64 R := by
    rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide)]; exact hx1
  obtain x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 (dirFlagOf d) := by rw [o₄ _ (by decide), o₃ _ (by decide), r₂]
  obtain x3₄ : s₄.gpr .x3 = B := by rw [o₄ _ (by decide), r₃, o₂ _ (by decide)]; exact hB
  have x4₄ : s₄.gpr .x4 = BitVec.ofNat 64 slots := r₄
  obtain mem₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, kept_mem]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, kept_rd]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, kept_wr]
  show WP isa (prepareCall d) s _
  refine WP.seq (WP.of_runBlock ⟨s₄, by rw [runBlock_app, keepHead_ok, Option.bind_some]; exact eargs, ?_⟩)
  obtain hsep : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * slots⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; omega_arith))
  obtain w : WP isa (.call "vg_camellia_prepare_keys" prepareKeys) s₄ fun s' =>
      s'.rd = s₄.rd ∧ s'.wr = s₄.wr ∧ Frame [⟨B, 8 * slots⟩] s₄.mem s'.mem ∧
      Holds layout s'.mem B R (schedWords s.mem p R) (specDir d) := by
    refine WP.call (k := prepAArch64) prep_correct (rd := [⟨p, 272⟩]) (wr := [⟨B, 8 * slots⟩]) ?_
      (Covers.append_left (Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [rd₄']; exact hin))
        (Covers.right (by rw [wr₄']; exact ws_covers hs)))
      (by rw [wr₄']; exact ws_covers hs) (fun s' hrd hwr _ hf _ _ hpost => ⟨hrd, hwr, hf, ?_⟩) (by lit_decide)
    · have g0 : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x0 = p := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₄]
      obtain g1 : ((s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x1).toNat = R := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₄, toNat_rounds hRr]
      obtain g2 : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x2 =
          BitVec.ofNat 64 (dirFlagOf d) := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x2₄]
      obtain g3 : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x3 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), x3₄]
      obtain g4 : ((s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x4).toNat = slots := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), x4₄, toNat_slots]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.withRegions_rd, g0]
      · rw [State.withRegions_wr, g3, g4, Nat.mul_comm]
      · rw [g0, g3, g4, Nat.mul_comm]; exact hsep
      · rw [g0]; exact hfit
      · rw [g3, g4]; omega_arith
      · rw [g1]; exact hRr
      · rw [g2]; cases d <;> decide
      · rw [g4, size_eq]
    · obtain ⟨hH, -⟩ := hpost
      have hm : (s'.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).mem = s'.mem := rfl
      obtain hm₀ : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).mem = s.mem := by
        rw [State.withRegions_mem, State.callEntry_mem, mem₄]
      obtain g0 : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x0 = p := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₄]
      obtain g1 : ((s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x1).toNat = R := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₄, toNat_rounds hRr]
      obtain g2 : Proof.Camellia.Prepared.directionOf
          ((s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x2).toNat = specDir d := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x2₄]
        cases d <;> rfl
      obtain g3 : (s₄.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]).gpr .x3 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), x3₄]
      change Holds layout _ _ _ _ _ at hH
      rw [hm, hm₀, g0, g1, g2, g3] at hH
      exact hH
  obtain ⟨t₅, s₅, e₅, rd₅, wr₅, f₅, hH⟩ := w
  refine WP.seq ⟨t₅, s₅, e₅, ?_⟩
  obtain ⟨s₆, e₆, b₆, -, x23₆, x24₆, x4₆, m₆, rd₆, wr₆⟩ := keepTail_kept (s := s) (s₁ := s₅) fun v hv => by
    rw [call_keepsV prepareKeys_vsafe e₅ v hv, v₄ v hv]
  refine WP.of_runBlock ⟨s₆, e₆, ⟨hRr, ?_, by rw [x4₆, hx1]⟩, by rw [b₆, hB], x23₆, x24₆, ?_,
    by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [m₆]
    have := readyAt_of_words (words_of_holds hH)
    rw [ofSpecDir_specDir, ← hws] at this
    exact this
  · rw [m₆, ← mem₄]
    exact f₅.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (Nat.le_refl _)⟩

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Camellia.Subkeys} {d : Spec.Camellia.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Camellia.blocksAt m' D n = Spec.Camellia.ecb K d (Spec.Camellia.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Camellia.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      blockFn K d (Spec.Camellia.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  rw [Proof.Camellia.ecb_eq] at this
  simpa [Spec.Camellia.blocksAt, hj] using this

/-- The table survives what a batch keeps. -/
theorem holds_of_keeps {R : Nat} (hR : R = 18 ∨ R = 24) {m m' : Mem} {B : Addr} {w : List (BitVec 64)}
    {d : Spec.Camellia.Direction} (h : Holds layout m B R w d)
    (hk : Keeps B slots layout.cryptScratch m m') : Holds layout m' B R w d := fun r hr i hi => by
  have hr' := hr
  rw [layout_table] at hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  obtain hg4 : R / 6 ≤ 4 := by omega_arith
  rw [hk (r.1 + i) (by rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_arith) (by
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [evenSlot_eq, m3Slot_eq, keySlot_eq, savedSlot_eq, tailSlot_eq]
    rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_arith)]
  exact h r hr i hi

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : Ready d s B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Ready d s' B k ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (bufAddr (dirCore d) B j) 16 =
        dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (bufAddr (dirCore d) B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨hRr, hready, hx4⟩ := hr
  simp only at hRr hready hx4 ⊢
  have hfB := hs.fit
  rw [total_eq] at hfB
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok (kept .x4 s) .x0 .x4
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .x1 sb
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := Modes.AArch64.movz_ok s₃ .x2 (v := slots) (by decide)
  obtain eargs : runBlock isa ([movR .x0 .x4] ++ ([movR .x1 sb] ++ [.movz .x .x2 (BitVec.ofNat 16 slots) 0]))
      (kept .x4 s) = some s₄ := by
    rw [runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄]
  obtain v₄ : ∀ v ∈ keepVs, s₄.v v = (kept .x4 s).v v := fun v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact runBlock_keepV (by decide) eargs
  obtain x0₄ : s₄.gpr .x0 = BitVec.ofNat 64 R := by
    rw [o₄ _ (by decide), o₃ _ (by decide), r₂]; exact hx4
  obtain x1₄ : s₄.gpr .x1 = B := by rw [o₄ _ (by decide), r₃, o₂ _ (by decide)]; exact hB
  have x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 slots := r₄
  obtain mem₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, kept_mem]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, kept_rd]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, kept_wr]
  show WP isa cryptCall s _
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show keepHead = keepHeadWith .x4 from rfl, runBlock_app, keepHead_ok, Option.bind_some]; exact eargs, ?_⟩)
  obtain hH : Holds layout s.mem B R ws (specDir d) := by
    refine holds_of_words ?_
    rw [ofSpecDir_specDir]
    exact words_of_readyAt hready
  obtain w : WP isa (.call "vg_camellia_crypt_prepared" cryptPrepared) s₄ fun s' =>
      s'.rd = s₄.rd ∧ s'.wr = s₄.wr ∧ Frame [⟨B, 8 * slots⟩] s₄.mem s'.mem ∧
      Spec.Camellia.blocksAt s'.mem (B + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords R ws) (specDir d)
          (Spec.Camellia.blocksAt s.mem (B + BitVec.ofNat 64 layout.buf) layout.blocks) ∧
      Keeps B slots layout.cryptScratch s.mem s'.mem := by
    refine WP.call (k := cryptAArch64) crypt_correct (rd := []) (wr := [⟨B, 8 * slots⟩]) ?_
      (Covers.append_left Covers.nil (Covers.right (by rw [wr₄']; exact ws_covers hs)))
      (by rw [wr₄']; exact ws_covers hs) (fun s' hrd hwr _ hf _ _ hpost => ⟨hrd, hwr, hf, ?_⟩) (by lit_decide)
    · have g0 : ((s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x0).toNat = R := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₄, toNat_rounds hRr]
      obtain g1 : (s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x1 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₄]
      obtain g2 : ((s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x2).toNat = slots := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x2₄, toNat_slots]
      obtain hm₀ : (s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).mem = s.mem := by
        rw [State.withRegions_mem, State.callEntry_mem, mem₄]
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.withRegions_wr, g1, g2, Nat.mul_comm]
      · rw [g1, g2]; omega_arith
      · rw [g0]; exact hRr
      · rw [g2, size_eq]
      · rw [g0, g1, hm₀]; exact ⟨ws, specDir d, hH⟩
    · obtain ⟨hB', hK⟩ := hpost
      have hm : (s'.withRegions [] [⟨B, 8 * slots⟩]).mem = s'.mem := rfl
      obtain hm₀ : (s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).mem = s.mem := by
        rw [State.withRegions_mem, State.callEntry_mem, mem₄]
      obtain g0 : ((s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x0).toNat = R := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), x0₄, toNat_rounds hRr]
      obtain g1 : (s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x1 = B := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), x1₄]
      obtain g2 : ((s₄.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .x2).toNat = slots := by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), x2₄, toNat_slots]
      rw [hm, hm₀, g0, g1] at hB'
      rw [hm, hm₀, g1, g2] at hK
      exact ⟨hB' ws (specDir d) hH, hK⟩
  obtain ⟨t₅, s₅, e₅, rd₅, wr₅, f₅, hE, hK⟩ := w
  refine WP.seq ⟨t₅, s₅, e₅, ?_⟩
  obtain ⟨s₆, e₆, b₆, -, x23₆, x24₆, x4₆, m₆, rd₆, wr₆⟩ := keepTail_kept (s := s) (s₁ := s₅) fun v hv => by
    rw [call_keepsV cryptPrepared_vsafe e₅ v hv, v₄ v hv]
  refine WP.of_runBlock ⟨s₆, e₆, by rw [b₆, hB], x23₆, x24₆, ⟨hRr, ?_, by rw [x4₆, hx4]⟩, ?_,
    fun j hj => ?_, by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [m₆]
    have := readyAt_of_words (words_of_holds (holds_of_keeps hRr hH hK))
    rw [ofSpecDir_specDir] at this
    exact this
  · rw [m₆, ← mem₄]
    exact f₅.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (Nat.le_refl _)⟩
  · have hj' : j < 8 := hj
    obtain ha : bufAddr (dirCore d) B j = B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := by
      rw [VG.Offset.add_add]; rfl
    rw [ha, dirCipher_bytes, bytesAt_eq_blockAt, m₆, blockAt_of_ecb hE hj']

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 2 := rfl

/-- Camellia's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher]
  layout := ⟨by cases d <;> decide, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide,
    by cases d <;> decide⟩
  keyRegs_ok := by cases d <;> decide
  regs_ok := by cases d <;> decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame := ready_frame
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

/-- Camellia's core for encryption, for CTR. -/
abbrev modeCoreSpec : CoreSpec modeCore := dirCoreSpec .encrypt

end VG.Proof.Camellia.AArch64

end

end

/-! ### `Camellia.AArch64.Serial.Prepare`, which only this module used -/

section

/-! # Preparing the constant S-box and raw Camellia schedule -/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial

theorem tableWord_byte : ∀ h < 32, ∀ j < 8,
    (tableWord h).extractLsb' (8*j) 8 = Spec.Camellia.sbox1Table.getD (8*h+j) 0 := fun h _ j hj => by
  have r8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  unfold tableWord
  rw [r8, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons,
    List.foldl_cons, List.foldl_cons, List.foldl_nil]
  exact VG.Proof.Sm4.AArch64.pack8_byte (fun j => Spec.Camellia.sbox1Table.getD (8 * h + j) 0) hj

theorem table_run {s : State} {B : Addr}
    (hb : s.gpr .x5 = B)
    (hw : (⟨B, 8*396⟩ : Region) ∈ s.wr) :
    ∃ t, runBlock isa table s = some t ∧
      (∀ j < 32, t.mem.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) ∧
      (∀ r, r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨B,256⟩] s.mem t.mem := by
  have hrange : tableEntries.map (·.1) = List.range 32 := by
    simp [tableEntries,List.map_map,Function.comp_def]
  obtain ⟨t,he,hv,_,hg,hd,hw',hf⟩ := VG.Proof.Sm4.AArch64.setSlotsN_ok 32
    (by decide) tableEntries (s := s) hb hw
    (fun kv hk => by
      simp only [tableEntries,List.mem_map,List.mem_range] at hk
      obtain ⟨i,hi,rfl⟩ := hk
      exact hi)
    (by rw [hrange]; exact List.nodup_range)
  have hbt : t.gpr .x5 = B := (hg _ (by decide)).trans hb
  refine ⟨t,he,?_,hg,hd,hw',hf⟩
  intro j hj
  have hjmem : (j,tableWord j) ∈ tableEntries :=
    List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
  have h := hv (j,tableWord j) hjmem
  simp only [VG.Proof.Sm4.AArch64.slotW,VG.AArch64.Straight.wordAddr,VG.Impl.Aes.AArch64.sb,hbt] at h
  exact h

theorem table_bytes {m : Mem} {B : Addr}
    (h : ∀ j < 32, m.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) :
    ∀ j < 256, m (B + BitVec.ofNat 64 j) = Spec.Camellia.sbox1Table.getD j 0 := by
  intro j hj
  have e := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) (h (j/8) (by omega_using [hj]))
  change (m.read (B + BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _ at e
  rw [Mem.extractLsb'_read _ _ (by omega_using []),tableWord_byte _ (by omega_using [hj]) _ (by omega_using []),
    VG.Offset.add_add,show 8*(j/8)+j%8 = j by omega_using []] at e
  exact e

/-- The same table setup under any permissions covering its scratch space. -/
theorem table_wp {s : State} {B : Addr}
    (hb : s.gpr .x5 = B) (hw : InRegions s.wr B (8*396)) :
    WP isa (.block table) s fun t =>
      (∀ j < 32, t.mem.readW (B + BitVec.ofNat 64 (8*j)) 64 = tableWord j) ∧
      (∀ r, r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨B,256⟩] s.mem t.mem := by
  let u := s.withRegions [] [⟨B,8*396⟩]
  obtain ⟨t,he,hv,hg,hd,hw',hf⟩ := table_run (s := u) hb List.mem_cons_self
  obtain ⟨tr,t',hex,heq⟩ := (WP.of_runBlock ⟨t,he,rfl⟩ :
    WP isa (.block table) u (fun t' => t' = t))
  subst t'
  have hcov : Covers u.wr s.wr := Covers.one hw
  have hread : Covers (u.rd ++ u.wr) (s.rd ++ s.wr) := Covers.right hcov
  have ew := VG.AArch64.Exec.widen (s := u) (s' := t) (rd := s.rd) (wr := s.wr) hex hread hcov
  refine ⟨tr,t.withRegions s.rd s.wr,?_,hv,hg,rfl,rfl,hf⟩
  simpa only [u,State.withRegions_withRegions,State.withRegions_self] using ew

end VG.Proof.Camellia.AArch64.Serial

end

end

/-! ### `Camellia.AArch64.Serial.Copy`, which only this module used -/

section

/-! # Copy the expanded schedule using the existing checked block copier -/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Camellia.AArch64 (CopyInv copyBlocks_bounded_wp)

theorem copySchedule_wp {s : State}
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 272)
    (hw : InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 256) 272)
    (hsep : Region.Disjoint ⟨s.gpr .x0,272⟩ ⟨s.gpr .x5 + BitVec.ofNat 64 256,272⟩) :
    WP isa copySchedule s fun t =>
      (∀ j < 272, t.mem (s.gpr .x5 + BitVec.ofNat 64 256 + BitVec.ofNat 64 j) =
        s.mem (s.gpr .x0 + BitVec.ofNat 64 j)) ∧
      Frame [⟨s.gpr .x5 + BitVec.ofNat 64 256,272⟩] s.mem t.mem ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  let a := s.write .x .x14 (s.gpr .x0)
  let b := a.write .x .x15 (a.gpr .x5 + BitVec.ofNat 64 256)
  let c := b.write .x .x17 17
  have regs : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → c.gpr r = s.gpr r := by
    intro r h14 h15 h17
    simp only [c,b,a,gpr_write_of_ne _ _ _ h14,gpr_write_of_ne _ _ _ h15,gpr_write_of_ne _ _ _ h17]
  have c14 : c.gpr .x14 = s.gpr .x0 := by simp [c,b,a,State.write]
  have c15 : c.gpr .x15 = s.gpr .x5 + BitVec.ofNat 64 256 := by simp [c,b,a,State.write]
  have c17 : c.gpr .x17 = 17 := by simp [c,State.write]
  unfold copySchedule
  refine WP.seq (WP.of_runBlock ⟨c,?_,?_⟩)
  · have ea : exec (VG.Impl.Aes.AArch64.movR .x14 .x0) s = some a := by
      simp [VG.Impl.Aes.AArch64.movR,exec,State.read,a]
    have eb : exec (.addImm .x .x15 .x5 256) a = some b := by
      rw [exec_addImm_x (by decide)]
      simp [State.read,b]
    have ec : exec (.movz .x .x17 17 0) b = some c := rfl
    rw [runBlock_cons,ea,runStep_some,runBlock_cons,eb,runStep_some,
      runBlock_cons,ec,runStep_some,runBlock_nil]
  · have hA : ∀ j < 34, InRegions (c.rd ++ c.wr) (s.gpr .x0 + BitVec.ofNat 64 (8*j)) 8 := by
      intro j hj
      exact CallLay.inRegions_sub hr (by omega_using [hj]) (by decide)
    have hB : ∀ j < 34, InRegions c.wr (s.gpr .x5 + BitVec.ofNat 64 256 + BitVec.ofNat 64 (8*j)) 8 := by
      intro j hj
      exact CallLay.inRegions_sub hw (by omega_using [hj]) (by decide)
    have inv : CopyInv (s.gpr .x0) (s.gpr .x5+ BitVec.ofNat 64 256) 17 c 0 c := by
      refine ⟨?_,?_,?_,fun _ h => absurd h (by omega_using []),Frame.refl _ _,fun _ _ _ _ _ => rfl,rfl,rfl⟩
      · simpa using c14
      · simpa using c15
      · simpa using c17
    refine WP.mono (copyBlocks_bounded_wp (by decide) (by decide) hA hB hsep inv) fun t ht =>
      ⟨ht.copied,ht.frame,fun r h14 h15 h17 h21 =>
        (ht.regs r h14 h15 h17 h21).trans (regs r h14 h15 h17),ht.rd,ht.wr⟩

end VG.Proof.Camellia.AArch64.Serial

end

end


/-! # Preparing the serial core under the existing Camellia key contract -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Modes.AArch64 (ScrIn coreRegion)
open VG.Proof.Camellia.AArch64 (KeyArgs)

theorem prepare_wp {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr .x5 = B) (hs : ScrIn s B core.total)
    (hR : (⟨B,8*core.total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa core.prepare s fun t => Ready t.mem B k ∧ t.gpr .x1 = BitVec.ofNat 64 k.1 ∧
      t.gpr .x5 = B ∧ t.gpr .x23 = s.gpr .x23 ∧ t.gpr .x24 = s.gpr .x24 ∧
      Frame [⟨B,528⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨p,hp,hx1,hrounds,hws,hin,hfit,hdis⟩ := hk
  have hw : InRegions s.wr B (8*396) :=
    ⟨_,hs.wr,by change (⟨B,3344⟩ : Region).Contains B 3168; simp [Region.Contains]⟩
  have hkey : Region.Disjoint ⟨p,272⟩ ⟨B,8*core.total⟩ := hdis _ hR
  change WP isa (.seq (.block table) copySchedule) s _
  refine WP.seq (WP.mono (table_wp hB hw) fun a ⟨aw,ag,ard,awr,af⟩ => ?_)
  have ab : a.gpr .x5 = B := (ag _ (by decide)).trans hB
  have ap : a.gpr .x0 = p := (ag _ (by decide)).trans hp
  have preserved : ∀ j < 272, a.mem (p+BitVec.ofNat 64 j) = s.mem (p+BitVec.ofNat 64 j) := by
    intro j hj
    exact af.bytes (R := ⟨p,272⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hkey.sub_right (Region.sub_prefix (by decide))) (by decide : 272 ≤ 2^64) hj
  have readKey : InRegions (a.rd ++ a.wr) (a.gpr .x0) 272 := by
    rw [ard,awr,ap]
    exact ⟨_,List.mem_append_left _ hin,Region.contains_self _ _⟩
  have writeKey : InRegions a.wr (a.gpr .x5+BitVec.ofNat 64 256) 272 := by
    rw [awr,ab]
    exact ⟨_,hs.wr,VG.Offset.contains_base B (by decide : 256+272 ≤ 3344) (by decide)⟩
  have sepKey : Region.Disjoint ⟨a.gpr .x0,272⟩ ⟨a.gpr .x5+BitVec.ofNat 64 256,272⟩ := by
    rw [ap,ab]
    exact hkey.sub_right (VG.Offset.sub_base B (by decide : 256+272 ≤ 3344))
  refine WP.mono (copySchedule_wp readKey writeKey sepKey) fun t ⟨tc,tf,tg,trd,twr⟩ => ?_
  have tab : ∀ j < 256, t.mem (B+BitVec.ofNat 64 j) = Spec.Camellia.sbox1Table.getD j 0 := by
    intro j hj
    have tf' : Frame [⟨B+BitVec.ofNat 64 256,272⟩] a.mem t.mem := by simpa only [ab] using tf
    rw [tf'.bytes (R := ⟨B,256⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact VG.Offset.base_disjoint B (by decide : 256 ≤ 256) (by decide : 256+272 ≤ 2^64))
      (by decide : 256 ≤ 2^64) hj]
    exact table_bytes aw j hj
  have keyWords : ∀ i < Spec.Camellia.scheduleLength k.1,
      Spec.Camellia.wordAt t.mem (B+BitVec.ofNat 64 (256+8*i)) = k.2.getD i 0 := by
    intro i hi
    have hi34 : i < 34 := by
      simp only [Spec.Camellia.scheduleLength] at hi
      omega_using [hrounds, hi]
    rw [hws,VG.Proof.Camellia.schedWords_getD _ _ hi]
    unfold Spec.Camellia.wordAt Spec.Camellia.bytesAt
    congr 1
    apply List.map_congr_left
    intro j hj
    have hj8 : j < 8 := List.mem_range.mp hj
    rw [VG.Offset.add_add,VG.Offset.add_add]
    have e := tc (8*i+j) (by omega_using [hi34, hj8])
    rw [ab,ap,preserved _ (by omega_using [hi34, hj8]),VG.Offset.add_add] at e
    simpa only [show 256+8*i+j = 256+(8*i+j) by omega_using []] using e
  refine ⟨⟨hrounds,tab,keyWords⟩,?_,?_,?_,?_,?_,trd.trans ard,twr.trans awr⟩
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans
      ((ag _ (by decide)).trans hx1)
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans ab
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans (ag _ (by decide))
  · exact (tg _ (by decide) (by decide) (by decide) (by decide)).trans (ag _ (by decide))
  · refine (af.sub (fun r hr => ?_)).trans (tf.sub (fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,Region.sub_prefix (by decide : 256 ≤ 528)⟩
    · simp only [List.mem_singleton] at hr; subst r
      exact ⟨_,List.mem_cons_self,by rw [ab]; exact VG.Offset.sub_base B (by decide : 256+272 ≤ 528)⟩

end VG.Proof.Camellia.AArch64.Serial

end

end

/-! ### `Camellia.AArch64.Serial.Layout`, which this module and modules that import it used -/

section

/-!
# The serial core's working space as `Proof.Camellia.Prepared`'s layout

The table of `layout` holds the words `w` (`Holds`) exactly when the serial
core's table is ready for them (`Ready`): the S-box's bytes, then the
words, the most significant byte first (`holds_of_ready`,
`ready_of_holds`). `keeps_of_frame`: a working space changed only within
one range keeps every byte outside it.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.Serial

open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Camellia.Prepared (Holds Keeps)

/-- The S-box's table, then the schedule's words as stored (the most
significant byte first), then the block at byte 768. -/
def layout : Prepared.Layout where
  table rounds := [(0, 256), (256, 8 * Spec.Camellia.scheduleLength rounds)]
  encode _ w _ i :=
    if i < 256 then Spec.Camellia.sbox1Table.getD i 0
    else (Spec.Camellia.wordBytes (w.getD ((i - 256) / 8) 0)).getD ((i - 256) % 8) 0
  buf := 768
  blocks := 1
  prepScratch := [(0, 528)]
  cryptScratch := [(768, 16)]
  size := 8 * core.total

theorem wordBytes_getD (w : BitVec 64) {j : Nat} (hj : j < 8) :
    (Spec.Camellia.wordBytes w).getD j 0 = Proof.Camellia.byteOf w j := by
  simp [Spec.Camellia.wordBytes, Proof.Camellia.byteOf, hj]

theorem layout_table (R : Nat) : layout.table R = [(0, 256), (256, 8 * Spec.Camellia.scheduleLength R)] := rfl

theorem encode_sbox {R : Nat} {w : List (BitVec 64)} {d : Spec.Camellia.Direction} {i : Nat} (hi : i < 256) :
    layout.encode R w d i = Spec.Camellia.sbox1Table.getD i 0 := by
  simp only [layout, hi, ↓reduceIte]

theorem encode_word {R : Nat} {w : List (BitVec 64)} {d : Spec.Camellia.Direction} (i : Nat) :
    layout.encode R w d (256 + i) = Proof.Camellia.byteOf (w.getD (i / 8) 0) (i % 8) := by
  simp only [layout, show ¬ 256 + i < 256 by omega_using [], ↓reduceIte, Nat.add_sub_cancel_left]
  exact wordBytes_getD _ (Nat.mod_lt _ (by decide))

/-- A ready table holds its words, for either direction (the encoding does
not depend on it). -/
theorem holds_of_ready {m : Mem} {B : Addr} {k : Nat × List (BitVec 64)} (h : Ready m B k)
    (d : Spec.Camellia.Direction) : Holds layout m B k.1 k.2 d := by
  intro r hr i hi
  rw [layout_table] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · simp only [Nat.zero_add] at hi ⊢
    rw [encode_sbox hi]
    exact h.sbox i hi
  · dsimp only at hi ⊢
    rw [encode_word, ← h.keys (i / 8) (by omega_using [hi]), Proof.Camellia.byteOf_wordAt _ _ (Nat.mod_lt _ (by decide)),
      VG.Offset.add_add, show 256 + 8 * (i / 8) + i % 8 = 256 + i by omega_using []]

/-- A table holding the words of 18 or 24 rounds is ready for them. -/
theorem ready_of_holds {m : Mem} {B : Addr} {R : Nat} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (hR : R = 18 ∨ R = 24) (h : Holds layout m B R w d) : Ready m B (R, w) := by
  refine ⟨hR, fun j hj => ?_, fun i hi => ?_⟩
  · have := h (0, 256) (by rw [layout_table]; simp) j hj
    simp only [Nat.zero_add] at this
    rw [this, encode_sbox hj]
  · dsimp only at hi
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hb := h (256, 8 * Spec.Camellia.scheduleLength R) (by rw [layout_table]; simp)
      (8 * i + (7 - k / 8)) (by omega_using [hi])
    dsimp only at hb
    rw [Proof.Camellia.getLsbD_wordAt _ _ hk, VG.Offset.add_add,
      show 256 + 8 * i + (7 - k / 8) = 256 + (8 * i + (7 - k / 8)) by omega_using [], hb, encode_word,
      show (8 * i + (7 - k / 8)) / 8 = i by omega_using [], show (8 * i + (7 - k / 8)) % 8 = 7 - k / 8 by omega_using [],
      Proof.Camellia.getLsbD_byteOf _ (by omega_using []) (Nat.mod_lt _ (by decide)),
      show 56 - 8 * (7 - k / 8) + k % 8 = k by omega_using [hk]]

/-- A working space changed only within the `n` bytes at offset `e` keeps
every byte outside them. -/
theorem keeps_of_frame {m m' : Mem} {B : Addr} {len e n : Nat}
    (hf : Frame [⟨B + BitVec.ofNat 64 e, n⟩] m m') (hn : 0 < n) (fit : B.toNat + len * 8 ≤ 2 ^ 64)
    (he : e + n ≤ 8 * len) : Keeps B len [(e, n)] m m' := fun i hi hout =>
  hf _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have ho := hout (e, n) (List.mem_singleton_self _)
    exact Proof.Camellia.not_contains_off B ho (by omega_using [fit, hi]) hn (by omega_using [fit, he])

/-- What changed within the working space and only within one range of it
changed only within that range. -/
theorem frame_of_keeps {m m' : Mem} {B : Addr} {len e n : Nat}
    (hf : Frame [⟨B, 8 * len⟩] m m') (hk : Keeps B len [(e, n)] m m') (he : e + n ≤ 8 * len)
    (fit : 8 * len < 2 ^ 64) : Frame [⟨B + BitVec.ofNat 64 e, n⟩] m m' := by
  intro x hx
  by_cases hc : (⟨B, 8 * len⟩ : Region).Contains x 1
  · simp only [Region.Contains] at hc
    have hx' : x = B + BitVec.ofNat 64 (x - B).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    rw [hx']
    refine hk _ (by omega) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    by_contra hne
    refine hx _ (List.mem_singleton_self _) ?_
    rw [hx', show (x - B).toNat = e + ((x - B).toNat - e) by omega, ← VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega) (by omega)
  · exact hf x fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc

end VG.Proof.Camellia.AArch64.Serial

end

end

/-!
# The serial core's two functions meet their contracts

`prep_correct` and `crypt_correct`: `vg_camellia_prepare_encrypt_keys`
and `vg_camellia_encrypt_prepared` meet `prepAArch64` and `cryptAArch64`,
with `layout`. Each runs the serial core's half
(`prepare_wp`, `crypt_wp`) from the state narrowed to the core's 418 slots
of the working space, and then from the whole working space
(`Exec.widen`). The preparation changes only the table's 528 bytes, a
block only its own 16. A block is encrypted under the words of any table
its working space holds: the run from it is the run from the table the
precondition gives (`Exec.det`).
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.Serial

open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Proof.Camellia (schedWords)
open VG.Proof.Modes.AArch64 (ScrIn runBlock_app)
open VG.Proof.Camellia.Prepared (Holds Keeps)

/-! ## Narrowing the working space -/

/-- `s` with its writable region the core's slots at `ws`. -/
abbrev narrowWs (s : State) (ws : Addr) : State := s.withRegions s.rd [⟨ws, 8 * core.total⟩]

/-- A run from the narrowed state is a run from `s`, to the state with `s`'s regions. -/
theorem exec_widenWs {c : Prog isa} {s s' : State} {t : List Leak} {ws : Addr} {len : Nat}
    (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * core.total ≤ len) (h : Exec isa c (narrowWs s ws) t s') :
    Exec isa c s t (s'.withRegions s.rd s.wr) := by
  have hc : Covers [⟨ws, 8 * core.total⟩] s.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨ws, len⟩, by rw [hw]; simp, 0, by rw [BitVec.add_zero], by show 0 + 8 * core.total ≤ len; omega_using [hl]⟩
  have := Exec.widen h (Covers.append (Covers.refl _) hc) hc
  rw [show (narrowWs s ws).rd = s.rd from rfl] at this
  rwa [State.withRegions_withRegions, State.withRegions_self] at this

theorem size_eq : layout.size = 3344 := rfl

theorem toNat_ofNat_rounds {R : BitVec 64} : BitVec.ofNat 64 R.toNat = R := by
  apply BitVec.eq_of_toNat_eq; simp

/-- The callee-saved registers and the rest of the ABI. -/
theorem abi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hv : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r) : abiPreserved s s' :=
  ⟨hg, Exec.sp he, hv⟩

/-! ## The preparation -/

/-- `vg_camellia_prepare_encrypt_keys` on AArch64. -/
def prepAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 272⟩
    let ws : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩
    s.rd = [sched] ∧ s.wr = [ws] ∧ sched.Disjoint ws ∧ (s.gpr .x0).toNat + 272 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + (s.gpr .x3).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 18 ∨ (s.gpr .x1).toNat = 24) ∧ layout.size ≤ 8 * (s.gpr .x3).toNat
  post s s' :=
    Holds layout s'.mem (s.gpr .x2) (s.gpr .x1).toNat
        (Proof.Camellia.Prepared.wordsAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) .encrypt ∧
      Keeps (s.gpr .x2) (s.gpr .x3).toNat layout.prepScratch s.mem s'.mem
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- The preparation from the narrowed state: the table ready, only its 528
bytes changed, `x21` kept. -/
theorem prepareEncrypt_wp {s : State} {B p : Addr} {R : Nat} (hB : s.gpr .x2 = B) (hp : s.gpr .x0 = p)
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 R) (hR : R = 18 ∨ R = 24)
    (hs : ScrIn s B core.total) (hin : (⟨p, 272⟩ : Region) ∈ s.rd) (hfit : p.toNat + 272 ≤ 2 ^ 64)
    (hdis : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * core.total⟩) :
    WP isa prepareEncrypt s fun t => Ready t.mem B (R, schedWords s.mem p R) ∧
      Frame [⟨B, 528⟩] s.mem t.mem ∧ t.gpr .x21 = s.gpr .x21 ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := Modes.AArch64.movR_ok s sb .x2
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movR_ok s₁ .x9 .x21
  have e : runBlock isa [movR sb .x2, movR .x9 .x21] s = some s₂ := by
    rw [show [movR sb .x2, movR .x9 .x21] = [movR sb .x2] ++ [movR .x9 .x21] from rfl, runBlock_app, e₁,
      Option.bind_some, e₂]
  have b₂ : s₂.gpr sb = B := by rw [o₂ _ (by decide), r₁, hB]
  have x9₂ : s₂.gpr .x9 = s.gpr .x21 := by rw [r₂, o₁ _ (by decide)]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have hk : VG.Proof.Camellia.AArch64.KeyArgs s₂ [⟨B, 8 * core.total⟩] (R, schedWords s.mem p R) :=
    ⟨p, by rw [o₂ _ (by decide), o₁ _ (by decide), hp], by rw [o₂ _ (by decide), o₁ _ (by decide), hx1], hR,
      by rw [mem₂], by rw [rd₂']; exact hin, hfit, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hdis⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, e, ?_⟩)
  have w := WP.gprs (rs := [.x9]) (prepare_wp b₂ ⟨by rw [wr₂']; exact hs.wr, hs.fit⟩ List.mem_cons_self hk)
    (by lit_decide) (by lit_decide)
  refine WP.seq (WP.mono w fun t h => ?_)
  obtain ⟨⟨tr, -, -, -, -, tf, trd, twr⟩, t9⟩ := h
  obtain ⟨u, eu, ru, -, mu, rdu, wru⟩ := Modes.AArch64.movR_ok t .x21 .x9
  refine WP.of_runBlock ⟨u, eu, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mu]; exact tr
  · rw [mu, ← mem₂]; exact tf
  · rw [ru, t9 _ List.mem_cons_self, x9₂]
  · rw [rdu, trd, rd₂']
  · rw [wru, twr, wr₂']

theorem prep_correct (s : State) (hs : prepAArch64.pre s) :
    ∃ t s', Exec isa prepareEncrypt s t s' ∧ abiPreserved s s' ∧ prepAArch64.post s s' := by
  obtain ⟨hrd, hwr, dSW, fitK, fitW, hR, hsz⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * core.total ≤ (s.gpr .x3).toNat * 8 := by
    show 3344 ≤ _; omega_using [hsz]
  have w := prepareEncrypt_wp (s := narrowWs s (s.gpr .x2)) (R := (s.gpr .x1).toNat) rfl rfl
    toNat_ofNat_rounds.symm hR ⟨by simp, by show (s.gpr .x2).toNat + 3344 ≤ 2 ^ 64; omega_using [fitW, hsz]⟩
    (by simp [hrd]) fitK (dSW.sub_right (Region.sub_prefix hl))
  obtain ⟨t, s', he, ⟨hr, hf, h21, -, -⟩, hg⟩ := WP.gprs (rs := [.x19, .x20, .x22, .x23, .x24, .x25, .x26,
    .x27, .x28, .x30]) w (by lit_decide) (by lit_decide)
  have he' := exec_widenWs hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', abi_of he' (Exec.preservedV he' (by lit_decide)) fun r hr' => ?_,
    ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact h21
      | exact hg _ (by simp)
  · exact holds_of_ready hr .encrypt
  · exact keeps_of_frame (e := 0) (by simpa only [narrowWs, State.withRegions_mem, State.withRegions_gpr,
      BitVec.add_zero] using hf) (by decide) fitW (by omega_using [hsz])

/-! ## A block -/

/-- `vg_camellia_encrypt_prepared` on AArch64. -/
def cryptAArch64 : Contract AArch64.isa where
  pre s :=
    let ws : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat * 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .x0).toNat = 18 ∨ (s.gpr .x0).toNat = 24) ∧ layout.size ≤ 8 * (s.gpr .x2).toNat ∧
      ∃ w, Holds layout s.mem (s.gpr .x1) (s.gpr .x0).toNat w .encrypt
  post s s' :=
    (∀ w, Holds layout s.mem (s.gpr .x1) (s.gpr .x0).toNat w .encrypt →
      Spec.Camellia.blocksAt s'.mem (s.gpr .x1 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords (s.gpr .x0).toNat w) .encrypt
          (Spec.Camellia.blocksAt s.mem (s.gpr .x1 + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (s.gpr .x1) (s.gpr .x2).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

/-- A block from the narrowed state: encrypted under the ready table's
words, only its 16 bytes changed. -/
theorem encryptPrepared_wp {s : State} {B : Addr} {k : Nat × List (BitVec 64)} (hB : s.gpr .x1 = B)
    (hx0 : s.gpr .x0 = BitVec.ofNat 64 k.1) (hs : ScrIn s B core.total) (ready : Ready s.mem B k) :
    WP isa encryptPrepared s fun t =>
      Frame [⟨B + BitVec.ofNat 64 768, 16⟩] s.mem t.mem ∧
      Spec.Aes.bytesAt t.mem (B + BitVec.ofNat 64 768) 16 =
        Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (B + BitVec.ofNat 64 768) 16) := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := Modes.AArch64.movR_ok s sb .x1
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movR_ok s₁ .x1 .x0
  have e : runBlock isa [movR sb .x1, movR .x1 .x0] s = some s₂ := by
    rw [show [movR sb .x1, movR .x1 .x0] = [movR sb .x1] ++ [movR .x1 .x0] from rfl, runBlock_app, e₁,
      Option.bind_some, e₂]
  have b₂ : s₂.gpr sb = B := by rw [o₂ _ (by decide), r₁, hB]
  have x1₂ : s₂.gpr .x1 = BitVec.ofNat 64 k.1 := by rw [r₂, o₁ _ (by decide), hx0]
  have mem₂ : s₂.mem = s.mem := by rw [m₂, m₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, e, ?_⟩)
  refine WP.mono (crypt_wp b₂ ⟨by rw [wr₂, wr₁]; exact hs.wr, hs.fit⟩ (by rw [mem₂]; exact ready) x1₂)
    fun t h => ⟨?_, ?_⟩
  all_goals obtain ⟨-, -, -, -, -, tf, tc, -, -⟩ := h
  · rw [← mem₂]; exact tf
  · rw [tc, mem₂]

theorem blocks_of {B : Addr} {m m' : Mem} {K : Spec.Camellia.Subkeys}
    (h : Spec.Aes.bytesAt m' (B + BitVec.ofNat 64 768) 16 =
      Spec.Camellia.cipher K (Spec.Aes.bytesAt m (B + BitVec.ofNat 64 768) 16)) :
    Spec.Camellia.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Camellia.ecb K .encrypt (Spec.Camellia.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Camellia.ecb_eq]
  simp only [Spec.Camellia.blocksAt, layout, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
    BitVec.add_zero]
  rw [Proof.Camellia.bytesAt_eq_blockAt, Proof.Camellia.bytesAt_eq_blockAt, Spec.Camellia.cipher,
    Proof.Camellia.ofFn_toList] at h
  refine congrArg (fun b => [b]) ?_
  exact Vector.toList_inj.mp h

theorem blocks_of_ecb {B : Addr} {m m' : Mem} {K : Spec.Camellia.Subkeys}
    (h : Spec.Camellia.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Camellia.ecb K .encrypt (Spec.Camellia.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks)) :
    Spec.Aes.bytesAt m' (B + BitVec.ofNat 64 768) 16 =
      Spec.Camellia.cipher K (Spec.Aes.bytesAt m (B + BitVec.ofNat 64 768) 16) := by
  rw [Proof.Camellia.ecb_eq] at h
  simp only [Spec.Camellia.blocksAt, layout, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
    BitVec.add_zero] at h
  rw [Proof.Camellia.bytesAt_eq_blockAt, Proof.Camellia.bytesAt_eq_blockAt, Spec.Camellia.cipher,
    Proof.Camellia.ofFn_toList, (List.cons.inj h).1]
  rfl

theorem crypt_correct (s : State) (hs : cryptAArch64.pre s) :
    ∃ t s', Exec isa encryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptAArch64.post s s' := by
  obtain ⟨-, hwr, fitW, hR, hsz, w₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * core.total ≤ (s.gpr .x2).toNat * 8 := by
    show 3344 ≤ _; omega_using [hsz]
  have hsN : ScrIn (narrowWs s (s.gpr .x1)) (s.gpr .x1) core.total :=
    ⟨by simp, by show (s.gpr .x1).toNat + 3344 ≤ 2 ^ 64; omega_using [fitW, hsz]⟩
  have run := fun (w : List (BitVec 64)) (h : Holds layout s.mem (s.gpr .x1) (s.gpr .x0).toNat w .encrypt) =>
    encryptPrepared_wp (s := narrowWs s (s.gpr .x1)) (k := ((s.gpr .x0).toNat, w)) rfl
      toNat_ofNat_rounds.symm hsN (ready_of_holds hR h)
  obtain ⟨t, s', he, ⟨hf, -⟩, hg⟩ := WP.gprs (rs := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
    .x27, .x28, .x30]) (run w₀ hH) (by lit_decide) (by lit_decide)
  have he' := exec_widenWs hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', abi_of he' (Exec.preservedV he' (by lit_decide))
    fun r hr' => hg r (by simpa [preserved] using hr'), fun w hw => ?_, ?_⟩
  · obtain ⟨t₂, s₂, he₂, -, hc⟩ := run w hw
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    exact blocks_of hc
  · exact keeps_of_frame hf (by decide) fitW (by show 784 ≤ _; omega_using [hsz])

end VG.Proof.Camellia.AArch64.Serial
