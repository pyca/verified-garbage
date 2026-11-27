module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Core
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Modes
public import VerifiedGarbage.Spec.Camellia.Cbc
import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Camellia.PPC64LE.Group
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Camellia.Prepared
public import VerifiedGarbage.Proof.Camellia.PPC64LE.Ecb
import VerifiedGarbage.Proof.Camellia.PPC64LE.Crypt8
public import VerifiedGarbage.Impl.Camellia.PPC64LE.Prepared
meta import VerifiedGarbage.Proof.Camellia.Prepared
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Camellia.PPC64LE.Crypt8
meta import VerifiedGarbage.Impl.Camellia.PPC64LE.Prepared

/-! ### `Camellia.PPC64LE.PreparedVerified`, which only this module used -/

section

/-! ### `Camellia.PPC64LE.PreparedBody`, which this module and modules that import it used -/

section

/-!
# Camellia's prepared subkeys and batches on PPC64LE: the code

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

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (sb t0 t1 kp movR stS)
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

/-- `vg_camellia_prepare_keys`'s body, with its working space at `r6`
exactly ECB's scratch buffer. -/
theorem prepareBody_wp {s₀ : State} (hrd : s₀.rd = [⟨s₀.gpr .r3, 272⟩]) (hwr : s₀.wr = [⟨s₀.gpr .r6, 8 * slots⟩])
    (dSS : Region.Disjoint ⟨s₀.gpr .r3, 272⟩ ⟨s₀.gpr .r6, 8 * slots⟩)
    (fitK : (s₀.gpr .r3).toNat + 272 ≤ 2 ^ 64) (fitB : (s₀.gpr .r6).toNat + 8 * slots ≤ 2 ^ 64)
    (hR : (s₀.gpr .r4).toNat = 18 ∨ (s₀.gpr .r4).toNat = 24) :
    WP isa prepareKeys s₀ fun s' => (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      TableWordsAt (s₀.gpr .r4).toNat s'.mem (s₀.gpr .r6)
        (Proof.Camellia.Prepared.wordsAt s₀.mem (s₀.gpr .r3) (s₀.gpr .r4).toNat) (dirOf (s₀.gpr .r5)) := by
  let b := s₀.gpr .r6
  let sched := s₀.gpr .r3
  let R := (s₀.gpr .r4).toNat
  have hwS : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hrK : (⟨sched, 272⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  obtain ⟨s₁, e₁, b₁, g₁, sv₁, m₁, t₁, f₁, rd₁, wr₁⟩ := prologue_ok (a := .r6) (b := b) rfl hwS
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hk₁ : KeyPre s₁ b sched :=
    ⟨b₁, by rw [wr₁]; exact hwS, fitB, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  have r3₁ : s₁.gpr .r3 = sched := g₁ _ (by decide) (by decide)
  have r5₁ : s₁.gpr .r5 = s₀.gpr .r5 := g₁ _ (by decide) (by decide)
  have hz₁ : (s₁.gpr t0 == 0) = decide (R = 18) := by
    rw [t₁, show s₀.gpr .r4 = BitVec.ofNat 64 R by simp only [R, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega_arith
  have hz : isa.eval (.zero .d t0) s₁ = some (decide (g = 3)) := (eval_zero s₁ t0).trans (by
    rw [hz₁]; exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩))
  have hfitB := fitB
  rw [slots_eq] at hfitB
  refine WP.seq (WP.mono (Q := fun s₂ => KeysPost s₁ b sched g (permOf (dirOf (s₀.gpr .r5)) g) s₂) ?_ fun s₂ k₂ => ?_)
  · refine WP.ite (s₀.gpr .r5 == 0) ((eval_zero s₁ .r5).trans (by rw [r5₁])) (fun h => ?_) (fun h => ?_)
    · have : dirOf (s₀.gpr .r5) = .encrypt := by simp only [dirOf, beq_iff_eq.mp h, ite_true]
      rw [this]; exact WP.mono (keys_wp .encrypt hg hz hk₁ r3₁ m₁) fun _ h => h.1
    · have h' : s₀.gpr .r5 ≠ 0 := fun e => by rw [e] at h; exact absurd h (by decide)
      have : dirOf (s₀.gpr .r5) = .decrypt := by simp only [dirOf, h', ite_false]
      rw [this]; exact WP.mono (keys_wp .decrypt hg hz hk₁ r3₁ m₁) fun _ h => h.1
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
  have hp : permOf (dirOf (s₀.gpr .r5)) g i < 8 * g + 2 := dirPerm_lt _ hi
  have hl : permOf (dirOf (s₀.gpr .r5)) g i < Spec.Camellia.scheduleLength R := by
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
      s'.gpr .r7 = s.gpr sb + BitVec.ofNat 64 (8 * keySlot + 512 * g) ∧
      (∀ r, r ≠ .r7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  exact addI_ok s .r7 sb (imm := 8 * keySlot + 512 * g) (by rw [keySlot_eq]; omega_arith)

/-- `vg_camellia_crypt_prepared`'s body, with its working space at `r4`
ECB's scratch buffer, holding the subkeys of the words `w` of `r3`'s
rounds in the order of `d`. -/
theorem cryptBody_wp {s₀ : State} (hwr : (⟨s₀.gpr .r4, 8 * slots⟩ : Region) ∈ s₀.wr)
    (fitB : (s₀.gpr .r4).toNat + 8 * slots ≤ 2 ^ 64) (hR : (s₀.gpr .r3).toNat = 18 ∨ (s₀.gpr .r3).toNat = 24)
    {w : List (BitVec 64)} {d : Dir} (hr : ReadyAt d (s₀.gpr .r3).toNat s₀.mem (s₀.gpr .r4) w) :
    WP isa cryptPrepared s₀ fun s' => (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      ReadyAt d (s₀.gpr .r3).toNat s'.mem (s₀.gpr .r4) w ∧
      Frame [⟨s₀.gpr .r4, 8 * keySlot⟩, ⟨s₀.gpr .r4 + BitVec.ofNat 64 (8 * savedSlot), 272⟩] s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.gpr sb = s₀.gpr .r4 ∧
      ∀ j < 8, Spec.Camellia.blockAt s'.mem (s₀.gpr .r4 + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        blockFn (Spec.Camellia.subkeysOfWords (s₀.gpr .r3).toNat w) (specDir d)
          (Spec.Camellia.blockAt s₀.mem (s₀.gpr .r4 + BitVec.ofNat 64 (8 * tailSlot + 16 * j))) := by
  generalize hb : s₀.gpr .r4 = b at hwr fitB hr ⊢
  let R := (s₀.gpr .r3).toNat
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega_arith
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .r4
  have b₁ : s₁.gpr sb = b := r₁.trans hb
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁]; exact hwr) b₁
  obtain ⟨s₃, e₃, t₃, o₃, m₃, rd₃, wr₃⟩ := subI_ok s₂ t0 .r3 (imm := 18) (by decide)
  have b₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), g₂, b₁]
  have hz₃ : isa.eval (.zero .d t0) s₃ = some (decide (g = 3)) := by
    rw [eval_zero, t₃, g₂, o₁ _ (by decide),
      show s₀.gpr .r3 = BitVec.ofNat 64 R by simp only [R, BitVec.ofNat_toNat, BitVec.setWidth_eq],
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
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => s₄.gpr .r7 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) ∧
      (∀ r, r ≠ .r7 → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr)
    (WP.ite (decide (g = 3)) hz₃ (fun h => ?_) (fun h => ?_)) fun s₄ ⟨r7₄, o₄, m₄, rd₄, wr₄⟩ => ?_)
  · have hg3 : g = 3 := of_decide_eq_true h
    obtain ⟨s', e', r7', o', m', rd', wr'⟩ := endAddr_ok s₃ (g := 3) (.inl rfl)
    exact WP.of_runBlock ⟨s', e', by rw [r7', b₃, hg3], o', m', rd', wr'⟩
  · have hg4 : g = 4 := by have := of_decide_eq_false h; omega_arith
    obtain ⟨s', e', r7', o', m', rd', wr'⟩ := endAddr_ok s₃ (g := 4) (.inr rfl)
    exact WP.of_runBlock ⟨s', e', by rw [r7', b₃, hg4], o', m', rd', wr'⟩
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
      bound := by rw [r7₄, b₄] }
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
  obtain ⟨s₆, e₆, rg₆, og₆, m₆, rd₆, wr₆⟩ := restore_ok (by rw [c₅.wr, wr₄, wr₃, wr₂, wr₁]; exact hwr) base₅ sv₅
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
    by rw [rd₆, c₅.rd, rd₄, rd₃, rd₂, rd₁], by rw [wr₆, c₅.wr, wr₄, wr₃, wr₂, wr₁],
    by rw [og₆ _ (by decide), base₅], fun j hj => ?_⟩
  · refine ⟨fun kv hkv => by rw [m₆]; exact c₅.masks.at base₅ kv hkv, fun i hi => (hr.2 i hi).congr fun j hj => ?_⟩
    have hg4 : (s₀.gpr .r3).toNat / 6 ≤ 4 := by omega_arith
    rw [entryW_eq, entryW_eq, m₆, hk5 _ (by omega_arith) (by rw [keySlot_eq, savedSlot_eq]; omega_arith)]
  · rw [m₆]
    have l₄ : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * savedSlot), 272⟩] s₀.mem s₄.mem := by
      rw [m₄, m₃, ← m₁]
      exact f₂.sub fun r hr => ⟨⟨b + BitVec.ofNat 64 (8 * savedSlot), 272⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub b (d := 8 * savedSlot) (n := 144) (e := 8 * savedSlot) (k := 272) (by omega_arith) (by omega_arith)⟩
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
    show Region.Disjoint _ ⟨b + BitVec.ofNat 64 (8 * savedSlot), 144⟩
    exact VG.Offset.disjoint b (.inr (by rw [savedSlot_eq, tailSlot_eq] <;> omega_arith)) (by rw [tailSlot_eq] <;> omega_arith)
      (by rw [savedSlot_eq]; omega_arith)

end VG.Proof.Camellia.PPC64LE

end

end

/-!
# Camellia's prepared subkeys and batches on PPC64LE meet their contracts

`crypt_correct`: `vg_camellia_crypt_prepared` against
`Proof.Camellia.Prepared`, with `layout`. (The modes run the preparation
inline, `prepareBody_wp`, rather than call it.) The body runs from the state
narrowed to ECB's scratch buffer (`cryptBody_wp`) and then from the whole
working space (`Exec.widen`), which it changes only where the narrowed run
may. A batch's blocks are ECB in the direction and under the subkeys of any
words whose table its working space holds: the run from it is the run from
the table the precondition gives (`Exec.det`).
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Camellia.PPC64LE
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
  exact ⟨Covers.append (fun _ _ h => h) h, h⟩

/-- A run from the narrowed state is a run from `s`, to the state with `s`'s regions. -/
theorem exec_widen {c : Prog isa} {s s' : State} {t : List Leak} {ws : Addr} {len : Nat}
    (hw : s.wr = [⟨ws, len⟩]) (hl : 8 * slots ≤ len) (h : Exec isa c (narrow s ws) t s') :
    Exec isa c s t (s'.withRegions s.rd s.wr) := by
  have := Exec.widen h (narrow_covers s hw hl).1 (narrow_covers s hw hl).2
  rwa [State.withRegions_withRegions, State.withRegions_self] at this

theorem size_eq : layout.size = 8 * slots := rfl

/-- The registers the bodies may write. -/
def bodyWrites : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
   .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- The callee-saved registers, from those the bodies restore and `r2`. -/
theorem helperAbi_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hlr : s'.lr = s.lr) (h₁ : ∀ i < 18, s'.gpr (sreg i) = s.gpr (sreg i)) (h₂ : s'.gpr .r2 = s.gpr .r2) :
    abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, hlr⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact h₂
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
  · exact h₁ 10 (by omega_using [])
  · exact h₁ 11 (by omega_using [])
  · exact h₁ 12 (by omega_using [])
  · exact h₁ 13 (by omega_using [])
  · exact h₁ 14 (by omega_using [])
  · exact h₁ 15 (by omega_using [])
  · exact h₁ 16 (by omega_using [])
  · exact h₁ 17 (by omega_using [])

/-! ## A batch -/

/-- `vg_camellia_crypt_prepared` on PPC64LE. -/
def cryptPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let ws : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat * 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .r3).toNat = 18 ∨ (s.gpr .r3).toNat = 24) ∧ layout.size ≤ 8 * (s.gpr .r5).toNat ∧
      ∃ w d, Holds layout s.mem (s.gpr .r4) (s.gpr .r3).toNat w d
  post s s' :=
    (∀ w d, Holds layout s.mem (s.gpr .r4) (s.gpr .r3).toNat w d →
      Spec.Camellia.blocksAt s'.mem (s.gpr .r4 + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords (s.gpr .r3).toNat w) d
          (Spec.Camellia.blocksAt s.mem (s.gpr .r4 + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (s.gpr .r4) (s.gpr .r5).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp

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

theorem crypt_correct (s : State) (hs : cryptPPC64LE.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptPPC64LE.post s s' := by
  obtain ⟨-, hwr, fitW, hR, hsz, w₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .r5).toNat * 8 := by omega_using [hsz]
  have hwN : (⟨(narrow s (s.gpr .r4)).gpr .r4, 8 * slots⟩ : Region) ∈ (narrow s (s.gpr .r4)).wr := by simp
  have fitN : ((narrow s (s.gpr .r4)).gpr .r4).toNat + 8 * slots ≤ 2 ^ 64 := by
    show (s.gpr .r4).toNat + 8 * slots ≤ 2 ^ 64; omega_using [fitW, hsz]
  have hn : cryptPrepared.noCalls = true := by lit_decide
  obtain ⟨t, s', he, ⟨h₁, hRd, hF, -, -, -, -⟩, h₃⟩ := WP.keep bodyWrites
    (cryptBody_wp hwN fitN hR (readyAt_of_words (words_of_holds hH))) (by lit_decide) hn
  have he' := exec_widen hwr hl he
  refine ⟨t, s'.withRegions s.rd s.wr, he', helperAbi_of he' (Exec.lr he' hn (by lit_decide)) h₁ (h₃.gpr (by decide)),
    fun w d hk => ?_, fun i hi hout => ?_⟩
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, -, hB₂⟩ := cryptBody_wp hwN fitN hR (readyAt_of_words (words_of_holds hk))
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

end VG.Proof.Camellia.PPC64LE

end

end

/-!
# Camellia's core for the modes on PPC64LE

`dirCoreSpec d`: Camellia's core for the direction `d`
(`Impl.Camellia.PPC64LE.dirCore d`) meets what the modes need of a core
(`Proof.Modes.PPC64LE.CoreSpec`), with the key the number of rounds and the
schedule's words, its cipher `Spec.Camellia.cipher` under them for
encryption and `Spec.Camellia.invCipher` for decryption. The key's
arguments are the schedule at `r3` and the number of rounds in `r28`, which
the modes keep (`KeptBut`); it is ready when the masks and the table of
subkeys in `d`'s order are in the core's slots (`ReadyAt`) and `r28` still
holds the number of rounds.

`prepare` runs the body of `vg_camellia_prepare_keys` (`prepareBody_wp`)
from the state narrowed to the schedule and the functions' 414 slots
(`WP.narrow`); the registers the body does not write (`prepWrites`, by
`WP.keep`) hold meanwhile the values the core must keep. `crypt` calls
`vg_camellia_crypt_prepared` (`WP.call`, with its contract on PPC64LE,
`cryptPPC64LE`) on the functions' slots; it writes neither `r6` nor `r10`,
which keep `sb` and `r3` across the call (`crypt_keeps`), and restores the
callee-saved registers, `r28` among them.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE.Mode

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.Camellia.PPC64LE VG.Proof.Camellia.PPC64LE
open VG.Impl.Modes.PPC64LE (mov)
open VG.Proof.Modes.PPC64LE (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)
open VG.Proof.Camellia (schedWords schedWords_getD wordAt_frame bytesAt_eq_blockAt ofFn_toList blockFn)

/-- The number of rounds in `r28` and the schedule at `r3`, outside the
regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  ∃ p : Addr, s.gpr .r3 = p ∧ s.gpr .r28 = BitVec.ofNat 64 k.1 ∧ (k.1 = 18 ∨ k.1 = 24) ∧
    k.2 = schedWords s.mem p k.1 ∧ (⟨p, 272⟩ : Region) ∈ s.rd ∧ p.toNat + 272 ≤ 2 ^ 64 ∧
    ∀ r ∈ rs, Region.Disjoint ⟨p, 272⟩ r

/-- The table of the subkeys of `k`'s rounds and words in the order of `d`,
and the number of rounds in `r28`. -/
def Ready (d : Dir) (s : State) (B : Addr) (_ : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  (k.1 = 18 ∨ k.1 = 24) ∧ ReadyAt d k.1 s.mem B k.2 ∧ s.gpr .r28 = BitVec.ofNat 64 k.1

theorem mask_range {kv : Nat × BitVec 64} (hkv : kv ∈ layerMasks) : 48 ≤ kv.1 ∧ kv.1 < 53 := by
  simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
    simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]

theorem toNat_rounds {R : Nat} (h : R = 18 ∨ R = 24) : (BitVec.ofNat 64 R).toNat = R := by
  rcases h with rfl | rfl <;> rfl

/-- The table survives what writes only bytes from the tail buffer on. -/
theorem readyAt_congr {d : Dir} {R : Nat} {m m' : Mem} {B : Addr} {w : List (BitVec 64)} (hR : R = 18 ∨ R = 24)
    (h : ReadyAt d R m B w)
    (hw : ∀ o, o + 8 ≤ 8 * tailSlot → m'.readW (B + BitVec.ofNat 64 o) 64 = m.readW (B + BitVec.ofNat 64 o) 64) :
    ReadyAt d R m' B w := by
  obtain ⟨hm, he⟩ := h
  obtain hg4 : R / 6 ≤ 4 := by omega_using [hR]
  refine ⟨fun kv hkv => ?_, fun i hi => (he i hi).congr fun j hj => ?_⟩
  · have hk := mask_range hkv
    rw [← hm kv hkv]
    exact hw (8 * kv.1) (by rw [tailSlot_eq]; omega_using [hk])
  · exact hw (8 * keySlot + 64 * i + 8 * j) (by rw [keySlot_eq, tailSlot_eq]; omega_using [hR, hi, hj])

/-- A word of the core's slots before the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {dir : Dir} {B : Addr} {o : Nat} (ho : o + 8 ≤ 8 * tailSlot) {r : Region}
    (hr : Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (blkRegion (dirCore dir) B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 o, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B (show o + 8 ≤ 8 * slots by rw [slots_eq]; rw [tailSlot_eq] at ho; omega_using [ho]))
  · refine Region.Disjoint.sub_right ?_ h
    show Region.Disjoint ⟨B + BitVec.ofNat 64 o, 8⟩ ⟨B + BitVec.ofNat 64 (8 * tailSlot), 4 * 4 * 8⟩
    exact VG.Offset.disjoint B (by simp only [tailSlot_eq] at ho ⊢; omega_using [ho])
      (by simp only [tailSlot_eq] at ho; omega_using [ho]) (by simp only [tailSlot_eq]; omega_using [])

theorem ready_frame {dir : Dir} {s s' : State} {B : Addr} {ws : List Region} {k : Nat × List (BitVec 64)}
    {rs : List Region} (h : Ready dir s B ws k) (hk : KeptBut s s') (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (blkRegion (dirCore dir) B)) :
    Ready dir s' B ws k := by
  obtain ⟨hR, hr, h28⟩ := h
  refine ⟨hR, readyAt_congr hR hr fun o ho => ?_, by rw [hk .r28 (by decide) (by decide) (by decide) (by decide), h28]⟩
  exact hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint ho (hd r hr)) (by decide)

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hk : KeptBut s s') (hrd : s'.rd = s.rd) (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, h28, hR, hws, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hk.r3, hp], by rw [hk .r28 (by decide) (by decide) (by decide) (by decide), h28],
    hR, ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hws]
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  obtain hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega_using [hR, hi]
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

/-! ## The bodies, narrowed -/

/-- The registers `vg_camellia_prepare_keys`'s body writes. -/
def prepWrites : List Reg :=
  [.r3, .r4, .r7, .r8, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
   .r27, .r28, .r29, .r30, .r31]

theorem prep_writes : writesOnly prepWrites prepareKeys = true := by lit_decide
theorem prep_noCalls : prepareKeys.noCalls = true := by lit_decide
theorem prep_noFrames : prepareKeys.noFrames = true := by lit_decide

/-- The registers the core keeps are `r3`, `r2` or restored by the bodies. -/
theorem kept_cases : ∀ r ∈ kept, r = .r3 ∨ r = .r2 ∨ ∃ i < 18, sreg i = r := by decide

theorem dirOf_dirBit (d : Dir) : dirOf (BitVec.ofNat 64 (dirBit d)) = d := by cases d <;> rfl

theorem dirBit_lt (d : Dir) : dirBit d < 2 ^ 15 := by cases d <;> decide

theorem slots_le (d : Dir) : slots ≤ (dirCore d).total := by simp [dirCore, modeSlots]

/-- The functions' slots, as a region of the writable ones. -/
theorem ws_covers {s : State} {B : Addr} {d : Dir} (hS : ScrIn s B (dirCore d).total) :
    Covers [⟨B, 8 * slots⟩] s.wr :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, hS.wr, 0, by simp, by have := slots_le d; simp only; omega_using [this]⟩

theorem sreg_not_parked : ∀ i < 18, sreg i ∉ [Reg.r0, .r4, .r5, .r6, .r9, .r10, .r11, .r12] := by decide

theorem sreg_ne_r3_r5 : ∀ i < 18, sreg i ≠ .r3 ∧ sreg i ≠ .r5 := by decide

/-! ## The preparation -/

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr .r5 = B) (hS : ScrIn s B (dirCore d).total)
    (hm : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready d s' B rs k ∧ s'.gpr .r5 = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, h28, hR, hws, hin, hfit, hdis⟩ := hk
  have hfB : B.toNat + 8 * slots ≤ 2 ^ 64 := by have := hS.fit; have := slots_le d; omega_arith
  have dSS : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * slots⟩ :=
    (hdis _ hm).sub_right (Region.sub_prefix (by have := slots_le d; omega_using [this]))
  -- The arguments, and the values to keep in registers the body does not write.
  let s₁ := (((((((s.write .r6 (s.gpr .r5)).write .r4 (s.gpr .r28)).write .r5 (BitVec.ofNat 64 (dirBit d))).write
    .r9 (s.gpr .r29)).write .r10 (s.gpr .r30)).write .r11 (s.gpr .r31)).write .r12 (s.gpr .r3)).write .r0 (s.gpr .r28)
  have e₁ : runBlock isa [mov .r6 .r5, mov .r4 .r28, .li .r5 (dirBit d), mov .r9 .r29, mov .r10 .r30,
      mov .r11 .r31, mov .r12 .r3, mov .r0 .r28] s = some s₁ := by
    simp only [mov, runBlock_cons, exec_or_self, exec_li (dirBit_lt d), runStep_some, runBlock_nil]
    simp only [s₁, gpr_write]; rfl
  have g₁ : ∀ r, r ∉ [Reg.r0, .r4, .r5, .r6, .r9, .r10, .r11, .r12] → s₁.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₁, gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]
  have v₁ : s₁.gpr .r6 = B ∧ s₁.gpr .r4 = BitVec.ofNat 64 k.1 ∧ s₁.gpr .r5 = BitVec.ofNat 64 (dirBit d) ∧
      s₁.gpr .r9 = s.gpr .r29 ∧ s₁.gpr .r10 = s.gpr .r30 ∧ s₁.gpr .r11 = s.gpr .r31 ∧
      s₁.gpr .r12 = s.gpr .r3 ∧ s₁.gpr .r0 = s.gpr .r28 ∧ s₁.gpr .r3 = p := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [s₁, gpr_write, hB, h28, hp]
  obtain ⟨r6₁, r4₁, r5₁, r9₁, r10₁, r11₁, r12₁, r0₁, r3₁⟩ := v₁
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hS₁ : ScrIn s₁ B (dirCore d).total := ⟨hS.wr, hS.fit⟩
  -- The body, narrowed to the schedule and the functions' slots.
  let N := s₁.withRegions [⟨p, 272⟩] [⟨B, 8 * slots⟩]
  have w := prepareBody_wp (s₀ := N) (by simp [N, r3₁]) (by simp [N, r6₁]) (by simpa [N, r3₁, r6₁] using dSS)
    (by simpa [N, r3₁] using hfit) (by simpa [N, r6₁] using hfB) (by simp [N, r4₁, toNat_rounds hR, hR])
  have hc : Covers ([⟨p, 272⟩] ++ [⟨B, 8 * slots⟩]) (s₁.rd ++ s₁.wr) :=
    Covers.append (Covers.of_mem fun r hr => by simp at hr; subst hr; exact hin)
      (ws_covers hS₁)
  refine WP.seq (WP.narrow (WP.keep prepWrites w prep_writes prep_noCalls) hc (ws_covers hS₁)
    (fun s₂ rd₂ wr₂ _ f₂ ⟨⟨sv₂, tab₂⟩, kp₂⟩ => ?_) prep_noFrames)
  have k₂ : ∀ r, r ∉ prepWrites → s₂.gpr r = s₁.gpr r := fun r hr => by
    simpa [N] using kp₂.gpr hr
  -- The kept values back.
  let s₃ := (((((s₂.write .r5 (s₂.gpr .r6)).write .r3 (s₂.gpr .r12)).write .r28 (s₂.gpr .r0)).write .r29
    (s₂.gpr .r9)).write .r30 (s₂.gpr .r10)).write .r31 (s₂.gpr .r11)
  refine WP.of_runBlock ⟨s₃, by
    simp only [mov, runBlock_cons, exec_or_self, runStep_some, runBlock_nil]
    simp only [s₃, gpr_write]; rfl, ?_⟩
  have g₃ : ∀ r, r ∉ [Reg.r3, .r5, .r28, .r29, .r30, .r31] → s₃.gpr r = s₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [s₃, gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
  have kp : ∀ r, r ∈ [Reg.r0, .r6, .r9, .r10, .r11, .r12, .r2] → s₂.gpr r = s₁.gpr r := fun r hr =>
    k₂ r (by revert hr; decide +revert)
  have v₃ : s₃.gpr .r5 = B ∧ s₃.gpr .r3 = s.gpr .r3 ∧ s₃.gpr .r28 = s.gpr .r28 ∧ s₃.gpr .r29 = s.gpr .r29 ∧
      s₃.gpr .r30 = s.gpr .r30 ∧ s₃.gpr .r31 = s.gpr .r31 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [s₃, gpr_write] <;> simp
    · rw [kp .r6 (by simp), r6₁]
    · rw [kp .r12 (by simp), r12₁]
    · rw [kp .r0 (by simp), r0₁]
    · rw [kp .r9 (by simp), r9₁]
    · rw [kp .r10 (by simp), r10₁]
    · rw [kp .r11 (by simp), r11₁]
  have m₃ : s₃.mem = s₂.mem := rfl
  refine ⟨⟨hR, ?_, by rw [v₃.2.2.1, h28]⟩, v₃.1, fun r hr => ?_, ?_, by rw [show s₃.rd = s₂.rd from rfl, rd₂]; rfl,
    by rw [show s₃.wr = s₂.wr from rfl, wr₂]; rfl⟩
  · rw [m₃, hws]
    have := readyAt_of_words tab₂
    simp only [N, State.withRegions_gpr, State.withRegions_mem, r4₁, r6₁, r5₁, r3₁, toNat_rounds hR,
      dirOf_dirBit] at this
    exact this
  · rcases kept_cases r hr with rfl | rfl | ⟨i, hi, rfl⟩
    · exact v₃.2.1
    · rw [g₃ _ (by decide), kp .r2 (by simp), g₁ _ (by decide)]
    · by_cases h28 : sreg i = .r28
      · rw [h28]; exact v₃.2.2.1
      by_cases h29 : sreg i = .r29
      · rw [h29]; exact v₃.2.2.2.1
      by_cases h30 : sreg i = .r30
      · rw [h30]; exact v₃.2.2.2.2.1
      by_cases h31 : sreg i = .r31
      · rw [h31]; exact v₃.2.2.2.2.2
      have hs := sreg_not_parked i hi
      rw [g₃ _ (by simp [h28, h29, h30, h31, (sreg_ne_r3_r5 i hi).1, (sreg_ne_r3_r5 i hi).2]), ← g₁ _ hs]
      simpa [N] using sv₂ i hi
  · exact f₂

/-! ## A batch -/

/-- `vg_camellia_crypt_prepared` writes neither `r6` nor `r10`. -/
theorem crypt_keeps : ∀ i ∈ instrs cryptPrepared, dstOf i ≠ some .r6 ∧ dstOf i ≠ some .r10 := by
  obtain h : (instrs cryptPrepared).all (fun i => dstOf i != some .r6 && dstOf i != some .r10) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem slots_lt : slots < 2 ^ 15 := by rw [slots_eq]; decide

theorem toNat_slots : (BitVec.ofNat 64 slots).toNat = slots := by rw [BitVec.toNat_ofNat, slots_eq]

/-- The table survives what a batch keeps. -/
theorem holds_of_keeps {R : Nat} {m m' : Mem} {B : Addr} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (hR : R = 18 ∨ R = 24) (h : Proof.Camellia.Prepared.Holds layout m B R w d)
    (hk : Proof.Camellia.Prepared.Keeps B slots layout.cryptScratch m m') :
    Proof.Camellia.Prepared.Holds layout m' B R w d := fun r hr i hi => by
  obtain hg : R / 6 ≤ 4 := by omega_using [hR]
  have hr' := hr
  rw [layout_table] at hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rw [hk (r.1 + i) (by rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_arith) (by
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [evenSlot_eq, m3Slot_eq, keySlot_eq, savedSlot_eq, tailSlot_eq]
    rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_arith)]
  exact h r hr i hi

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Camellia.Subkeys} {d : Spec.Camellia.Direction} {m m' : Mem} {D : Addr}
    {n : Nat} (h : Spec.Camellia.blocksAt m' D n = Spec.Camellia.ecb K d (Spec.Camellia.blocksAt m D n))
    {j : Nat} (hj : j < n) :
    Spec.Camellia.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      blockFn K d (Spec.Camellia.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  rw [Proof.Camellia.ecb_eq] at this
  simpa [Spec.Camellia.blocksAt, hj] using this

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {ws : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr .r5 = B) (hS : ScrIn s B (dirCore d).total) (hr : Ready d s B ws k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr .r5 = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready d s' B ws k ∧ Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hR, hrd, h28⟩ := hr
  have hfB : B.toNat + 8 * (dirCore d).total ≤ 2 ^ 64 := hS.fit
  obtain hH : Proof.Camellia.Prepared.Holds layout s.mem B k.1 k.2 (specDir d) :=
    holds_of_words (by rw [ofSpecDir_specDir]; exact words_of_readyAt hrd)
  show WP isa cryptCall s _
  refine WP.seq (wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ =>
    wp_li slots_lt fun s₅ u₅ => wp_nil ?_)
  obtain g₅ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r10 → s₅.gpr r = s.gpr r :=
    fun r h3 h4 h5 h6 h10 => by
      rw [u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h6, u₁.other r h10]
  obtain r3₅ : s₅.gpr .r3 = BitVec.ofNat 64 k.1 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h28]
  obtain r4₅ : s₅.gpr .r4 = B := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hB]
  have r5₅ : s₅.gpr .r5 = BitVec.ofNat 64 slots := u₅.gpr
  obtain r6₅ : s₅.gpr .r6 = B := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hB]
  obtain r10₅ : s₅.gpr .r10 = s.gpr .r3 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr]
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain c3 : ((s₅.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .r3).toNat = k.1 := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r3₅, toNat_rounds hR]
  obtain c4 : (s₅.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .r4 = B := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r4₅]
  obtain c5 : ((s₅.callEntry.withRegions [] [⟨B, 8 * slots⟩]).gpr .r5).toNat = slots := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r5₅, toNat_slots]
  obtain hm₀ : (s₅.callEntry.withRegions [] [⟨B, 8 * slots⟩]).mem = s.mem := by
    rw [State.withRegions_mem, State.callEntry_mem, m₅]
  obtain cov : Covers [⟨B, 8 * slots⟩] s₅.wr := by rw [wr₅]; exact ws_covers hS
  refine WP.seq (WP.call (k := cryptPPC64LE) crypt_correct (rd := []) (wr := [⟨B, 8 * slots⟩]) ?_
    (Covers.append_left Covers.nil (Covers.right cov)) cov (fun s' hrd' hwr' _ hf hpres hnw hpost => ?_)
    (by lit_decide))
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [State.withRegions_wr, c4, c5, Nat.mul_comm]
    · rw [c4, c5]; have := slots_le d; omega_using [hfB, this]
    · rw [c3]; exact hR
    · rw [c5, size_eq]
    · rw [c3, c4, hm₀]; exact ⟨k.2, specDir d, hH⟩
  · obtain ⟨hE, hK⟩ := hpost
    have hm : (s'.withRegions [] [⟨B, 8 * slots⟩]).mem = s'.mem := rfl
    rw [hm, hm₀, c3, c4] at hE
    rw [hm, hm₀, c4, c5] at hK
    obtain hE' := hE k.2 (specDir d) hH
    obtain r6' : s'.gpr .r6 = B := by
      rw [hnw .r6 (by decide) fun i hi => (crypt_keeps i hi).1, r6₅]
    obtain r10' : s'.gpr .r10 = s.gpr .r3 := by
      rw [hnw .r10 (by decide) fun i hi => (crypt_keeps i hi).2, r10₅]
    obtain r28' : s'.gpr .r28 = s.gpr .r28 := by
      rw [hpres .r28 (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    refine wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_nil ⟨?_, fun r hr => ?_, ⟨hR, ?_, ?_⟩, ?_,
      fun j hj => ?_, by rw [u₇.rd, u₆.rd, hrd', rd₅], by rw [u₇.wr, u₆.wr, hwr', wr₅]⟩
    · rw [u₇.other _ (by decide), u₆.gpr, r6']
    · by_cases e3 : r = .r3
      · subst e3; rw [u₇.gpr, u₆.other _ (by decide), r10']
      obtain hp : r ∈ preserved := by
        simp only [kept, List.mem_cons] at hr
        rcases hr with rfl | h
        · exact absurd rfl e3
        · exact h
      obtain hne : ∀ r ∈ preserved, r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r10 := by decide
      obtain ⟨h4, h5, h6, h10⟩ := hne r hp
      rw [u₇.other r e3, u₆.other r h5, hpres r hp, g₅ r e3 h4 h5 h6 h10]
    · rw [u₇.mem, u₆.mem]
      exact readyAt_of_words (by rw [← ofSpecDir_specDir d]; exact words_of_holds (holds_of_keeps hR hH hK))
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), r28', h28]
    · rw [u₇.mem, u₆.mem, ← m₅]; exact hf
    · have hj8 : j < 8 := hj
      have ha : blkAddr (dirCore d) B j = B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := rfl
      show Spec.Aes.bytesAt s₇.mem (blkAddr (dirCore d) B j) 16 =
        dirCipher d _ (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) 16)
      rw [dirCipher_bytes, bytesAt_eq_blockAt, u₇.mem, u₆.mem, ha, blockAt_of_ecb hE' hj8]

/-- Camellia's core meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher, dirCore]
  layout := ⟨by cases d <;> decide, .inr rfl, by cases d <;> decide, by cases d <;> decide, by cases d <;> decide⟩
  keyArgs_congr h e r _ _ f := keyArgs_congr h e r f
  ready_frame h e _ _ _ f _ hd := ready_frame h e f hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.Camellia.PPC64LE.Mode
