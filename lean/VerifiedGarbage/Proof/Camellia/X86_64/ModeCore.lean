module

public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Impl.Camellia.X86_64.Ctr
public import VerifiedGarbage.Spec.Camellia.Cbc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Camellia.X86_64.Lit
import VerifiedGarbage.Proof.Camellia.X86_64.PairSum
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Camellia.X86_64.Lit
meta import VerifiedGarbage.Proof.Camellia.X86_64.PairSum
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Camellia.Prepared
public import VerifiedGarbage.Proof.Camellia.X86_64.Ecb
import VerifiedGarbage.Proof.Camellia.X86_64.Group
import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.Impl.Camellia.X86_64.Prepared
import VerifiedGarbage.Proof.Modes.X86_64.Steps
meta import VerifiedGarbage.Proof.Camellia.Prepared
meta import VerifiedGarbage.Proof.Camellia.X86_64.Ecb
meta import VerifiedGarbage.Proof.Camellia.X86_64.Group
meta import VerifiedGarbage.Proof.Modes.X86_64.Setup
meta import VerifiedGarbage.Impl.Camellia.X86_64.Prepared
meta import VerifiedGarbage.Proof.Modes.X86_64.Steps

/-! ### `Camellia.X86_64.PreparedVerified`, which only this module used -/

section

/-! ### `Camellia.X86_64.PreparedBody`, which only this module used -/

section

/-!
# Camellia's batches under prepared subkeys on x86-64: the code

What `vg_camellia_crypt_prepared` reads (`layout`,
`Proof.Camellia.Prepared.Holds`) is the masks and the table that ECB's
rounds read (`ReadyAt`), word for word (`TableWordsAt`, `holds_of_words`,
`readyAt_of_words` and back): each of the table's words is the plane of its
subkey (`keyPlane`, the only words related to it by `HalfRel`,
`halfRel_eq`).

`cryptBody_wp` runs the function's body, with its working space exactly
ECB's scratch buffer: the working space to `sb`, the callee-saved registers
to their slots, the postwhitening's entry for the number of rounds to its
slot, the eight blocks (`crypt8_ok`), and the registers back.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Impl.Camellia (keyPlane)
open VG.Proof.Camellia (HalfRel blockFn)

/-- The masks' slots and the table's, as byte ranges. -/
def layout : Prepared.Layout where
  table rounds := [(8 * evenSlot, 40), (8 * keySlot, 64 * (8 * (rounds / 6) + 2))]
  encode rounds w d i := (preparedWord rounds w (ofSpecDir d) (i / 8)).extractLsb' (8 * (i % 8)) 8
  buf := 8 * tailSlot
  blocks := 8
  prepScratch := [(0, 8 * slots)]
  cryptScratch := [(0, 8 * evenSlot), (8 * (m3Slot + 1), 8 * (keySlot - m3Slot - 1)),
    (8 * endSlot, 8), (8 * savedSlot, 8 * (tailSlot + 16 - savedSlot))]
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
  obtain e1 := h (p % 8) (by omega_using []) (p / 8) (by omega_using [hp]) j hj
  obtain e2 := keyPlane_rel x (p % 8) (by omega_using []) (p / 8) (by omega_using [hp]) j hj
  rw [show 8 * (p / 8) + p % 8 = p by omega_using []] at e1 e2
  rw [e1, e2]

theorem keyEntry_eq (w : List (BitVec 64)) (g : Nat) (d : Dir) (e : Nat) :
    keyEntry w g d e = w.getD (permOf d g e) 0 := by
  cases d <;> rfl

theorem ofSpecDir_specDir (d : Dir) : ofSpecDir (specDir d) = d := by cases d <;> rfl

theorem specDir_ofSpecDir (d : Spec.Camellia.Direction) : specDir (ofSpecDir d) = d := by cases d <;> rfl

/-- The masks and the table of subkeys of `R` rounds in the order of `d`:
what ECB's rounds read. -/
def ReadyAt (d : Dir) (R : Nat) (m : Mem) (B : Addr) (w : List (BitVec 64)) : Prop :=
  MasksAt m B ∧ ∀ i < 8 * (R / 6) + 2, EntryOk m B i (keyEntry w (R / 6) d i)

/-- The words of the masks and the table for `R` rounds, in the working
space at `B`. -/
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
  congr 2; omega_using []

theorem layout_table (R : Nat) : layout.table R = [(384, 40), (768, 64 * (8 * (R / 6) + 2))] := rfl
theorem evenSlot_eq : evenSlot = 48 := rfl
theorem m3Slot_eq : m3Slot = 52 := rfl

theorem table_ranges (R o : Nat) :
    (∃ r ∈ layout.table R, ∃ i < r.2, o = r.1 + i) ↔
      (evenSlot ≤ o / 8 ∧ o / 8 ≤ m3Slot) ∨ (keySlot ≤ o / 8 ∧ o / 8 < keySlot + 8 * (8 * (R / 6) + 2)) := by
  rw [layout_table, evenSlot_eq, m3Slot_eq, keySlot_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨r, hr | hr, i, hi, rfl⟩ <;> subst hr <;> dsimp only at hi ⊢ <;> omega_using [hi]
  · intro h
    rcases h with h | h
    · exact ⟨_, .inl rfl, o - 384, by dsimp only; omega_using [h], by dsimp only; omega_using [h]⟩
    · exact ⟨_, .inr rfl, o - 768, by dsimp only; omega_using [h], by dsimp only; omega_using [h]⟩

theorem holds_of_words {R : Nat} {m : Mem} {B : Addr} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (h : TableWordsAt R m B w (ofSpecDir d)) : Proof.Camellia.Prepared.Holds layout m B R w d := by
  intro r hr i hi
  obtain hw := (table_ranges R (r.1 + i)).1 ⟨r, hr, i, hi, rfl⟩
  rw [word_byte_addr, byte_of_readW m _ (by omega_using []), h _ hw]
  rfl

theorem words_of_holds {R : Nat} {m : Mem} {B : Addr} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (h : Proof.Camellia.Prepared.Holds layout m B R w d) : TableWordsAt R m B w (ofSpecDir d) := by
  intro k hk
  simp only [Mem.readW, BitVec.setWidth_eq]
  refine Mem.read_eq_of_bytes fun j hj => ?_
  obtain ⟨r, hr, i, hi, ho⟩ := (table_ranges R (8 * k + j)).2 (by
    rw [show (8 * k + j) / 8 = k by omega_using [hj]]; exact hk)
  have := h r hr i hi
  rw [← ho, word_byte_addr, show (8 * k + j) / 8 = k by omega_using [hj], show (8 * k + j) % 8 = j by omega_using [hj]] at this
  rw [this]
  show (preparedWord R w (ofSpecDir d) ((8 * k + j) / 8)).extractLsb' (8 * ((8 * k + j) % 8)) 8 = _
  rw [show (8 * k + j) / 8 = k by omega_using [hj], show (8 * k + j) % 8 = j by omega_using [hj]]

theorem entryW_word (m : Mem) (B : Addr) (e j : Nat) :
    entryW m B e j = m.readW (wordAddr B (keySlot + 8 * e + j)) 64 := by
  rw [entryW, wordAddr, show 8 * (keySlot + 8 * e + j) = 8 * keySlot + 64 * e + 8 * j by omega_using []]

theorem preparedWord_entry (R : Nat) (w : List (BitVec 64)) (d : Dir) {e j : Nat} (hj : j < 8) :
    preparedWord R w d (keySlot + 8 * e + j) = keyPlane (keyEntry w (R / 6) d e) j := by
  obtain hc : ¬ (keySlot + 8 * e + j < keySlot) := by omega_using []
  simp only [preparedWord, hc, ↓reduceIte]
  rw [show (keySlot + 8 * e + j - keySlot) / 8 = e by omega_using [hj], show (keySlot + 8 * e + j - keySlot) % 8 = j by omega_using [hj]]

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
  rw [entryW_word, h _ (.inr (by omega_using [he, hj])), preparedWord_entry R w d hj]

theorem words_of_readyAt {R : Nat} {m : Mem} {B : Addr} {w : List (BitVec 64)} {d : Dir}
    (h : ReadyAt d R m B w) : TableWordsAt R m B w d := by
  intro k hk
  rcases hk with hk | hk
  · have hkv : ∃ kv ∈ layerMasks, kv.1 = k := by
      rw [evenSlot_eq, m3Slot_eq] at hk
      simp only [layerMasks, List.mem_cons, List.not_mem_nil, or_false]
      rcases (by omega_using [hk] : k = 48 ∨ k = 49 ∨ k = 50 ∨ k = 51 ∨ k = 52) with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, .inl rfl, rfl⟩
      · exact ⟨_, .inr (.inl rfl), rfl⟩
      · exact ⟨_, .inr (.inr (.inl rfl)), rfl⟩
      · exact ⟨_, .inr (.inr (.inr (.inl rfl))), rfl⟩
      · exact ⟨_, .inr (.inr (.inr (.inr rfl))), rfl⟩
    obtain ⟨kv, hkv, rfl⟩ := hkv
    rw [h.1 kv hkv, preparedWord_mask R w d hkv]
  · obtain ⟨e, j, hj, rfl⟩ : ∃ e j, j < 8 ∧ k = keySlot + 8 * e + j :=
      ⟨(k - keySlot) / 8, (k - keySlot) % 8, by omega_using [], by omega_using [hk]⟩
    obtain he : e < 8 * (R / 6) + 2 := by omega_using [hk]
    rw [← entryW_word, preparedWord_entry R w d hj]
    exact halfRel_eq (h.2 e he) hj

/-- The rounds with the subkeys in the order of `d` are its block function. -/
theorem crypt_spec (d : Dir) {R : Nat} (hR : R = 18 ∨ R = 24) (w : List (BitVec 64)) (blk : Spec.Camellia.Block) :
    Spec.Camellia.encodeBlock (cryptWords (R / 6) (keyEntry w (R / 6) d) (Spec.Camellia.decodeBlock blk)) =
      blockFn (Spec.Camellia.subkeysOfWords R w) (specDir d) blk := by
  cases d
  · simp only [blockFn, specDir, Spec.Camellia.encryptBlock, encryptWith_eq hR]; rfl
  · simp only [blockFn, specDir, Spec.Camellia.decryptBlock, decryptWith_eq hR]; rfl

/-! ## The body -/

theorem saveRegs_eq : saveRegs = (List.range 6).map fun i => st (savedSlot + i) (sreg i) := rfl

theorem restoreRegs_eq : restoreRegs = (List.range 6).map fun i => movS (sreg i) (savedSlot + i) := rfl

theorem sreg_ne_sb (i : Nat) : sreg i ≠ sb := by unfold sreg; split <;> decide

/-- The registers' saves write their slots alone. -/
theorem save_saved {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa saveRegs s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨wordAddr b savedSlot, 48⟩] s.mem s'.mem := by
  obtain ⟨s', e', v', f', g', rd', wr'⟩ := Proof.Modes.X86_64.stores_ok savedSlot sreg 6 s hb
    (fun i hi => ⟨_, hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [savedSlot_eq, slots_eq]; omega_using [hi]) (by rw [savedSlot_eq]; omega_using [hi])⟩)
    (by rw [savedSlot_eq]; omega_using [])
  exact ⟨s', by rw [saveRegs_eq]; exact e', v', g', rd', wr', f'⟩

/-- The registers' restores read their slots. -/
theorem restore_loads {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 6, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 6, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e', v', o', m', rd', wr'⟩ := Proof.Modes.X86_64.loads_ok savedSlot sreg 6 s hb
    (fun i _ => sreg_ne_sb i) (by decide)
    (fun i hi => ⟨_, List.mem_append_right _ hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [savedSlot_eq, slots_eq]; omega_using [hi]) (by rw [savedSlot_eq]; omega_using [hi])⟩)
  exact ⟨s', by rw [restoreRegs_eq]; exact e', fun i hi => by rw [v' i hi, hs i hi], o', m', rd', wr'⟩

/-- The entry of the postwhitening subkey, for `g` groups. -/
theorem endAddr_ok (s : State) (g : Nat) :
    ∃ s', runBlock isa (endAddr g) s = some s' ∧
      s'.gpr .rdi = s.gpr sb + (BitVec.ofNat 32 (8 * keySlot + 512 * g)).signExtend 64 ∧
      (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rdi sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rdi (BitVec.ofNat 32 (8 * keySlot + 512 * g))
  refine ⟨s₂, ?_, by rw [r₂, r₁], fun r h => by rw [o₂ r h, o₁ r h], by rw [m₂, m₁], by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩
  rw [endAddr, show ([movR .rdi sb, .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * keySlot + 512 * g)))] :
    List Instr) = [movR .rdi sb] ++ [.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * keySlot + 512 * g)))] from rfl,
    runBlock_append', e₁, Option.bind_some, e₂]

theorem signExtend_end {g : Nat} (hg : g = 3 ∨ g = 4) :
    (BitVec.ofNat 32 (8 * keySlot + 512 * g)).signExtend 64 = BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
  rcases hg with rfl | rfl <;> rfl

theorem signExtend_tail :
    (BitVec.ofNat 32 (8 * tailSlot)).signExtend 64 = BitVec.ofNat 64 (8 * tailSlot) := rfl

/-- `vg_camellia_crypt_prepared`'s body, with its working space at `rsi`
ECB's scratch buffer, holding the subkeys of the words `w` of `rdi`'s
rounds in the order of `d`. It leaves the working space's address in `sb`. -/
theorem cryptBody_wp {s₀ : State} (hwr : (⟨s₀.gpr .rsi, 8 * slots⟩ : Region) ∈ s₀.wr)
    (fitB : (s₀.gpr .rsi).toNat + 8 * slots ≤ 2 ^ 64) (hR : (s₀.gpr .rdi).toNat = 18 ∨ (s₀.gpr .rdi).toNat = 24)
    {w : List (BitVec 64)} {d : Dir} (hr : ReadyAt d (s₀.gpr .rdi).toNat s₀.mem (s₀.gpr .rsi) w) :
    WP isa cryptPrepared s₀ fun s' => (∀ i < 6, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      s'.gpr .rsp = s₀.gpr .rsp ∧ s'.gpr sb = s₀.gpr .rsi ∧
      ReadyAt d (s₀.gpr .rdi).toNat s'.mem (s₀.gpr .rsi) w ∧
      Frame [⟨s₀.gpr .rsi, 8 * keySlot⟩, ⟨wordAddr (s₀.gpr .rsi) endSlot, 8⟩,
        ⟨wordAddr (s₀.gpr .rsi) savedSlot, 8 * (tailSlot + 16 - savedSlot)⟩] s₀.mem s'.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      ∀ j < 8, Spec.Camellia.blockAt s'.mem (s₀.gpr .rsi + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        blockFn (Spec.Camellia.subkeysOfWords (s₀.gpr .rdi).toNat w) (specDir d)
          (Spec.Camellia.blockAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (8 * tailSlot + 16 * j))) := by
  generalize hb : s₀.gpr .rsi = b at hwr fitB hr ⊢
  let R := (s₀.gpr .rdi).toNat
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  obtain hg : g = 3 ∨ g = 4 := by omega_arith
  have hfit := fitB
  rw [slots_eq] at hfit
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .rsi
  obtain b₁ : s₁.gpr sb = b := r₁.trans hb
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_saved (b := b) (by rw [wr₁]; exact hwr) b₁
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := cmpImmZ_ok s₂ .rdi 18
  obtain b₃ : s₃.gpr sb = b := by rw [g₃, g₂, b₁]
  obtain hz₃ : s₃.zf = some (decide (g = 3)) := by
    rw [z₃, show (18 : BitVec 32).signExtend 64 = BitVec.ofNat 64 18 from rfl, g₂, o₁ _ (by decide),
      show s₀.gpr .rdi = BitVec.ofNat 64 R by simp only [R, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩)
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃], ?_⟩)
  -- The postwhitening's entry.
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => s₄.gpr .rdi = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) ∧
      (∀ r, r ≠ .rdi → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧ s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr)
    (WP.ite (decide (g = 3)) (by simp [X86_64.eval, hz₃]) (fun h => ?_) (fun h => ?_))
    fun s₄ ⟨rdi₄, o₄, m₄, rd₄, wr₄⟩ => ?_)
  · have hg3 : g = 3 := of_decide_eq_true h
    obtain ⟨s', e', x', o', m', rd', wr'⟩ := endAddr_ok s₃ 3
    exact WP.of_runBlock ⟨s', e', by rw [x', b₃, signExtend_end (.inl rfl), hg3], o', m', rd', wr'⟩
  · have hg4 : g = 4 := by have := of_decide_eq_false h; omega_arith
    obtain ⟨s', e', x', o', m', rd', wr'⟩ := endAddr_ok s₃ 4
    exact WP.of_runBlock ⟨s', e', by rw [x', b₃, signExtend_end (.inr rfl), hg4], o', m', rd', wr'⟩
  obtain b₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), b₃]
  obtain hw₄ : (⟨b, 8 * slots⟩ : Region) ∈ s₄.wr := by rw [wr₄, wr₃, wr₂, wr₁]; exact hwr
  obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := stReg_ok (s := s₄) (b := b) (k := endSlot) .rdi b₄
    ⟨_, hw₄, by rw [wordAddr]; exact VG.Offset.contains_base b (by rw [endSlot_eq, slots_eq]; omega_arith) (by rw [endSlot_eq]; omega_arith)⟩
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a⟩ := movR_ok s₅ .rdx sb
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₆a .rdx (BitVec.ofNat 32 (8 * tailSlot))
  obtain b₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₆a _ (by decide), g₅, b₄]
  obtain rdx₆ : s₆.gpr .rdx = b + BitVec.ofNat 64 (8 * tailSlot) := by
    rw [r₆, r₆a, g₅, b₄, signExtend_tail]
  obtain mem₆ : s₆.mem = s₄.mem.writeW (wordAddr b endSlot) (s₄.gpr .rdi) := by rw [m₆, m₆a, m₅]
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₆a, wr₅, wr₄, wr₃, wr₂, wr₁]
  obtain hw₆ : (⟨b, 8 * slots⟩ : Region) ∈ s₆.wr := by rw [wr₆']; exact hwr
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [show ([st endSlot .rdi] ++ tailAddr .rdx : List Instr) = [st endSlot .rdi] ++ ([movR .rdx sb] ++
      [.alu .add .rdx (.imm (BitVec.ofNat 32 (8 * tailSlot)))]) from rfl, runBlock_append', e₅, Option.bind_some,
      runBlock_append', e₆a, Option.bind_some, e₆], ?_⟩)
  -- The slots below the saved registers but the postwhitening's, unchanged.
  obtain slot₆ : ∀ k < savedSlot, k ≠ endSlot →
      s₆.mem.readW (wordAddr b k) 64 = s₀.mem.readW (wordAddr b k) 64 := fun k hk hne => by
    rw [mem₆, Proof.Modes.X86_64.readW_slot_write _ (by rw [savedSlot_eq] at hk; omega_arith)
      (by rw [endSlot_eq]; omega_arith), ite_eq_right hne, m₄, m₃, ← m₁]
    refine f₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint b (.inl (by rw [savedSlot_eq] at hk ⊢; omega_arith)) (by rw [savedSlot_eq] at hk; omega_arith)
      (by rw [savedSlot_eq]; omega_arith)
  obtain hcore : CorePre s₆ g (keyEntry w g d) :=
    { scr := by rw [b₆]; exact hw₆
      dat := fun k hk => ⟨_, hw₆, by
        rw [rdx₆, wordAddr, VG.Offset.add_add]
        exact VG.Offset.contains_base b (by rw [tailSlot_eq, slots_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)⟩
      sep := by
        rw [rdx₆, b₆]
        exact VG.Offset.disjoint_base b (by omega_arith) (by rw [tailSlot_eq]; omega_arith)
      fit := by rw [b₆]; exact fitB
      fitD := by
        rw [rdx₆, VG.Offset.toNat_add_ofNat, tailSlot_eq,
          Nat.mod_eq_of_lt (show 8 * 377 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega_arith)]
        omega_arith
      nk34 := by omega_arith
      masks := fun kv hkv => by
        show s₆.mem.readW (wordAddr (s₆.gpr sb) kv.1) 64 = kv.2
        obtain hk := mask_in hkv
        rw [evenSlot_eq, m3Slot_eq] at hk
        rw [b₆, slot₆ _ (by rw [savedSlot_eq]; omega_arith) (by rw [endSlot_eq]; omega_arith)]
        exact hr.1 kv hkv
      keys := fun i hi => by
        have := hr.2 i (by rw [hgR]; exact hi)
        rw [hgR] at this
        refine this.congr fun j hj => ?_
        rw [b₆, entryW_word, entryW_word, slot₆ _ (by rw [keySlot_eq, savedSlot_eq]; omega_arith)
          (by rw [keySlot_eq, endSlot_eq]; omega_arith)]
      hg := hg
      bound := by
        show s₆.mem.readW (wordAddr (s₆.gpr sb) endSlot) 64 = _
        rw [b₆, mem₆, Proof.Modes.X86_64.readW_slot_write _ (by rw [endSlot_eq]; omega_arith)
          (by rw [endSlot_eq]; omega_arith), ite_eq_left rfl, rdi₄] }
  refine WP.seq (WP.mono (crypt8_ok hcore) fun s₇ ⟨c₇, o₇⟩ => ?_)
  obtain base₇ : s₇.gpr sb = b := by rw [c₇.base, b₆]
  obtain f₇ : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩] s₆.mem s₇.mem := by
    have := c₇.frame; rw [b₆, rdx₆] at this; exact this
  obtain dis₇ : ∀ k, keySlot ≤ k → k < tailSlot → ∀ r ∈ [(⟨b, 8 * keySlot⟩ : Region),
      ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩], Region.Disjoint ⟨wordAddr b k, 8⟩ r := fun k h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [wordAddr]
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by omega_arith) (by rw [tailSlot_eq] at h2; omega_arith)
    · exact VG.Offset.disjoint b (.inl (by omega_arith)) (by rw [tailSlot_eq] at h2; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain sv₇ : Saved s₁ b s₇.mem := fun i hi => by
    rw [← sv₂ i hi]
    rw [f₇.readW (Region.contains_self _ _) (dis₇ _ (by rw [keySlot_eq, savedSlot_eq]; omega_arith)
      (by rw [savedSlot_eq, tailSlot_eq]; omega_arith)) (by decide), mem₆,
      Proof.Modes.X86_64.readW_slot_write _ (by rw [savedSlot_eq]; omega_arith) (by rw [endSlot_eq]; omega_arith),
      ite_eq_right (by rw [savedSlot_eq, endSlot_eq]; omega_arith), m₄, m₃]
  obtain ⟨s₈, e₈, rg₈, og₈, m₈, rd₈, wr₈⟩ := restore_loads (by rw [c₇.wr]; exact hw₆) base₇ sv₇
  obtain hk7 : ∀ k, keySlot ≤ k → k < savedSlot → k ≠ endSlot →
      s₇.mem.readW (wordAddr b k) 64 = s₀.mem.readW (wordAddr b k) 64 := fun k h1 h2 h3 => by
    rw [← slot₆ k h2 h3]
    exact f₇.readW (Region.contains_self _ _) (dis₇ k h1 (by rw [savedSlot_eq, tailSlot_eq] at *; omega_arith)) (by decide)
  obtain rsp₈ : s₈.gpr .rsp = s₀.gpr .rsp := by
    rw [og₈ _ (fun i _ => by unfold sreg; split <;> decide), c₇.keep _ (by decide) (by decide) (by decide),
      o₆ _ (by decide), o₆a _ (by decide), g₅, o₄ _ (by decide), g₃, g₂, o₁ _ (by decide)]
  refine WP.of_runBlock ⟨s₈, e₈, fun i hi => by rw [rg₈ i hi, o₁ _ (sreg_ne_sb i)], rsp₈,
    by rw [og₈ _ (fun i _ => (sreg_ne_sb i).symm), base₇], ?_, ?_,
    by rw [rd₈, c₇.rd, rd₆, rd₆a, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₈, c₇.wr, wr₆'], fun j hj => ?_⟩
  · refine ⟨fun kv hkv => by rw [m₈]; exact c₇.masks.at base₇ kv hkv, fun i hi => (hr.2 i hi).congr fun j hj => ?_⟩
    obtain hg4 : (s₀.gpr .rdi).toNat / 6 ≤ 4 := by omega_arith
    rw [entryW_word, entryW_word, m₈, hk7 _ (by omega_arith) (by rw [keySlot_eq, savedSlot_eq]; omega_arith)
      (by rw [keySlot_eq, endSlot_eq]; omega_arith)]
  · rw [m₈]
    obtain l₆ : Frame [⟨b, 8 * keySlot⟩, ⟨wordAddr b endSlot, 8⟩, ⟨wordAddr b savedSlot, 8 * (tailSlot + 16 - savedSlot)⟩]
        s₀.mem s₆.mem := by
      obtain f₂' : Frame [⟨wordAddr b savedSlot, 8 * (tailSlot + 16 - savedSlot)⟩] s₀.mem s₄.mem := by
        rw [m₄, m₃, ← m₁]
        exact f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr; subst hr; rw [wordAddr]
          exact VG.Offset.sub b (Nat.le_refl _) (by rw [savedSlot_eq, tailSlot_eq]; omega_arith)⟩
      obtain fw : Frame [⟨wordAddr b endSlot, 8⟩] s₄.mem s₆.mem := by
        rw [mem₆]
        exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
      exact (f₂'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
        (fw.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
    exact l₆.trans (f₇.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
        rw [wordAddr]
        exact VG.Offset.sub b (by rw [savedSlot_eq, tailSlot_eq] <;> omega_arith) (by rw [savedSlot_eq, tailSlot_eq] <;> omega_arith))
  · have := o₇ j hj
    simp only [blk, c₇.rdx, rdx₆] at this
    rw [m₈, show b + BitVec.ofNat 64 (8 * tailSlot + 16 * j) = b + BitVec.ofNat 64 (8 * tailSlot) +
      BitVec.ofNat 64 (16 * j) by rw [VG.Offset.add_add], this, ← hgR, crypt_spec d hR]
    refine congrArg _ (Vector.ext fun i hi => ?_)
    simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn]
    rw [show b + BitVec.ofNat 64 (8 * tailSlot) + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 i =
      b + BitVec.ofNat 64 (8 * tailSlot) + BitVec.ofNat 64 (16 * j + i) by
        simp only [VG.Offset.add_add, Nat.add_assoc]]
    obtain hdis : ∀ r ∈ ([⟨wordAddr b endSlot, 8⟩] : List Region),
        Region.Disjoint ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [wordAddr]
      exact VG.Offset.disjoint b (.inr (by rw [endSlot_eq, tailSlot_eq]; omega_arith)) (by rw [tailSlot_eq]; omega_arith)
        (by rw [endSlot_eq]; omega_arith)
    rw [mem₆, (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (⟨wordAddr b endSlot, 8⟩ : Region)) _
        (Region.contains_self _ _)).bytes hdis (by show (128 : Nat) ≤ 2 ^ 64; decide)
        (by show 16 * j + i < 128; omega_arith), m₄, m₃, ← m₁]
    refine f₂.bytes (R := ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩) (fun r hr => ?_)
      (by show (128 : Nat) ≤ 2 ^ 64; decide) (by show 16 * j + i < 128; omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr]
    exact VG.Offset.disjoint b (.inr (by rw [savedSlot_eq, tailSlot_eq] <;> omega_arith)) (by rw [tailSlot_eq] <;> omega_arith)
      (by rw [savedSlot_eq]; omega_arith)

end VG.Proof.Camellia.X86_64

end

end

/-!
# Camellia's batches under prepared subkeys on x86-64 meet their contract

`crypt_correct`: `vg_camellia_crypt_prepared` meets `cryptX86_64`, with
`layout`. The body runs from
the state narrowed to ECB's scratch buffer (`cryptBody_wp`) and then from
the whole working space (`Exec.widen`), which it changes only where the
narrowed run may. A batch's blocks are ECB in the direction and under the
subkeys of any words that its working space's table encodes: the run from
it is the run from the words the precondition gives (`Exec.det`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Proof.Camellia (specDir)
open VG.Proof.Camellia.Prepared (Holds Keeps)

theorem size_eq : layout.size = 8 * slots := rfl

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

/-! ## A batch -/

/-- `vg_camellia_crypt_prepared` on x86-64. -/
def cryptX86_64 : Contract X86_64.isa where
  pre s :=
    let ws : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat * 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [ws] ∧ ret.Disjoint ws ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat * 8 ≤ 2 ^ 64 ∧
      ((s.gpr .rdi).toNat = 18 ∨ (s.gpr .rdi).toNat = 24) ∧ layout.size ≤ 8 * (s.gpr .rdx).toNat ∧
      ∃ w d, Holds layout s.mem (s.gpr .rsi) (s.gpr .rdi).toNat w d
  post s s' :=
    (∀ w d, Holds layout s.mem (s.gpr .rsi) (s.gpr .rdi).toNat w d →
      Spec.Camellia.blocksAt s'.mem (s.gpr .rsi + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords (s.gpr .rdi).toNat w) d
          (Spec.Camellia.blocksAt s.mem (s.gpr .rsi + BitVec.ofNat 64 layout.buf) layout.blocks)) ∧
      Keeps (s.gpr .rsi) (s.gpr .rdx).toNat layout.cryptScratch s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

theorem blocks_of (B : Addr) {m m' : Mem} {k : Spec.Camellia.Subkeys} {d : Spec.Camellia.Direction}
    (h : ∀ j < 8, Spec.Camellia.blockAt m' (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)) =
        Proof.Camellia.blockFn k d (Spec.Camellia.blockAt m (B + BitVec.ofNat 64 (8 * tailSlot + 16 * j)))) :
    Spec.Camellia.blocksAt m' (B + BitVec.ofNat 64 layout.buf) layout.blocks =
      Spec.Camellia.ecb k d (Spec.Camellia.blocksAt m (B + BitVec.ofNat 64 layout.buf) layout.blocks) := by
  rw [Proof.Camellia.ecb_eq]
  simp only [Spec.Camellia.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  simp only [List.mem_range] at hj
  simp only [Function.comp_apply, VG.Offset.add_add]
  exact h j hj

/-- The masks' bytes, the same in two working spaces holding tables. -/
theorem mask_byte {m m' : Mem} {B : Addr} {R R' : Nat} {w w' : List (BitVec 64)} {d d' : Dir}
    (h : TableWordsAt R m B w d) (h' : TableWordsAt R' m' B w' d') {i : Nat}
    (hi : 8 * evenSlot ≤ i ∧ i < 8 * (m3Slot + 1)) :
    m' (B + BitVec.ofNat 64 i) = m (B + BitVec.ofNat 64 i) := by
  have hw : (evenSlot ≤ i / 8 ∧ i / 8 ≤ m3Slot) := by omega_using [hi]
  rw [word_byte_addr, byte_of_readW m' (wordAddr B (i / 8)) (j := i % 8) (by omega_using []),
    byte_of_readW m (wordAddr B (i / 8)) (j := i % 8) (by omega_using []), h _ (.inl hw), h' _ (.inl hw)]
  have hm : ∀ (R : Nat) (w : List (BitVec 64)) (d : Dir), preparedWord R w d (i / 8) =
      (layerMasks.find? (·.1 = i / 8)).elim 0 (·.2) := fun _ _ _ => by
    have hc : i / 8 < keySlot := by rw [keySlot_eq]; rw [m3Slot_eq] at hw; omega_using [hw]
    simp only [preparedWord, hc, ↓reduceIte]
  rw [hm, hm]

/-- The callee-saved registers, from those the body restores and `rsp`. -/
theorem helperGpr_of {s s' : State} (h₁ : ∀ i < 6, s'.gpr (sreg i) = s.gpr (sreg i))
    (h₂ : s'.gpr .rsp = s.gpr .rsp) (h₃ : s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64) :
    gprPreserved s s' := by
  refine ⟨fun r hr => ?_, h₃⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_using [])
  · exact h₁ 1 (by omega_using [])
  · exact h₂
  · exact h₁ 2 (by omega_using [])
  · exact h₁ 3 (by omega_using [])
  · exact h₁ 4 (by omega_using [])
  · exact h₁ 5 (by omega_using [])

theorem crypt_correct (s : State) (hs : cryptX86_64.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptX86_64.post s s' := by
  obtain ⟨-, hwr, dRW, fitW, hR, hsz, w₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .rdx).toNat * 8 := by omega_using [hsz]
  have hwN : (⟨(narrow s (s.gpr .rsi)).gpr .rsi, 8 * slots⟩ : Region) ∈ (narrow s (s.gpr .rsi)).wr := by simp
  have fitN : ((narrow s (s.gpr .rsi)).gpr .rsi).toNat + 8 * slots ≤ 2 ^ 64 := by
    show (s.gpr .rsi).toNat + 8 * slots ≤ 2 ^ 64; omega_using [fitW, hsz]
  obtain ⟨t, s', he, h₁, hrsp, -, hRd, hF, -, -, -⟩ :=
    cryptBody_wp hwN fitN hR (readyAt_of_words (words_of_holds hH))
  have he' := exec_widen hwr hl he
  have hfit := fitW
  rw [slots_eq] at hl
  have hF' : Frame [⟨s.gpr .rsi, 8 * keySlot⟩, ⟨wordAddr (s.gpr .rsi) endSlot, 8⟩,
      ⟨wordAddr (s.gpr .rsi) savedSlot, 8 * (tailSlot + 16 - savedSlot)⟩] s.mem s'.mem := hF
  refine ⟨t, s'.withRegions s.rd s.wr, he', abiPreserved_of_exec (c := cryptPrepared) (by lit_decide) he'
    (helperGpr_of h₁ hrsp ?_), fun w d hw => ?_, fun i hi hout => ?_⟩
  · refine hF'.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dRW.sub_right (Region.sub_prefix (by rw [keySlot_eq]; omega_using [hl]))
    · exact dRW.sub_right (VG.Offset.sub_base _ (by rw [endSlot_eq]; omega_using [hl]))
    · exact dRW.sub_right (VG.Offset.sub_base _ (by rw [savedSlot_eq, tailSlot_eq]; omega_using [hl]))
  · obtain ⟨t₂, s₂, he₂, -, -, -, -, -, -, -, hB₂⟩ :=
      cryptBody_wp hwN fitN hR (readyAt_of_words (words_of_holds hw))
    obtain ⟨-, rfl⟩ := Exec.det he he₂
    refine blocks_of _ fun j hj => ?_
    have := hB₂ j hj
    rw [specDir_ofSpecDir] at this
    exact this
  · simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [evenSlot_eq, m3Slot_eq, keySlot_eq, endSlot_eq, savedSlot_eq, tailSlot_eq] at hout
    by_cases hm : 384 ≤ i ∧ i < 424
    · exact mask_byte (words_of_holds hH) (words_of_readyAt hRd) (by rw [evenSlot_eq, m3Slot_eq]; omega_using [hm])
    · refine hF' _ fun r hr hc => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [Region.Contains, wordAddr] at hc
      · rw [Mem.sub_ofNat_toNat _ (by omega_using [fitW, hi]), keySlot_eq] at hc; omega_using [hout, hm, hc]
      · rw [VG.Offset.sub_toNat' _ (by rw [endSlot_eq]; omega_using []) (by omega_using [fitW, hi]), endSlot_eq] at hc
        split at hc <;> omega_arith
      · rw [VG.Offset.sub_toNat' _ (by rw [savedSlot_eq]; omega_using []) (by omega_using [fitW, hi]), savedSlot_eq, tailSlot_eq] at hc
        split at hc <;> omega_arith

/-- `cryptX86_64`, and what the body leaves in `sb`: the working space's
address, which the modes, calling it, keep there. -/
def cryptCallX86_64 : Contract X86_64.isa where
  pre := cryptX86_64.pre
  post s s' := cryptX86_64.post s s' ∧ s'.gpr VG.Impl.Aes.X86_64.sb = s.gpr .rsi
  pub := cryptX86_64.pub

theorem cryptCall_correct (s : State) (hs : cryptCallX86_64.pre s) :
    ∃ t s', Exec isa cryptPrepared s t s' ∧ abiPreserved s s' ∧ cryptCallX86_64.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := crypt_correct s hs
  obtain ⟨-, hwr, -, fitW, hR, hsz, w₀, d₀, hH⟩ := hs
  rw [size_eq] at hsz
  have hl : 8 * slots ≤ (s.gpr .rdx).toNat * 8 := by omega_using [hsz]
  obtain ⟨t₂, s₂, he₂, -, -, hsb, -⟩ := cryptBody_wp (s₀ := narrow s (s.gpr .rsi)) (by simp)
    (by show (s.gpr .rsi).toNat + 8 * slots ≤ 2 ^ 64; omega_using [fitW, hsz]) hR (readyAt_of_words (words_of_holds hH))
  obtain ⟨-, rfl⟩ := Exec.det he (exec_widen hwr hl he₂)
  exact ⟨t, _, he, ha, hp, hsb⟩

end VG.Proof.Camellia.X86_64

end

end

/-!
# Camellia's core for the modes on x86-64

`dirCoreSpec d`: Camellia's core for the direction `d`
(`Impl.Camellia.X86_64.dirCore d`) meets what the modes need of a core
(`Proof.Modes.X86_64.CoreSpec`), with the key the number of rounds and the
schedule's words, its cipher `Spec.Camellia.cipher` (encryption) or
`Spec.Camellia.invCipher` (decryption) under them, and the key ready when
the masks and the table of subkeys in `d`'s order are in the scratch buffer
(`ReadyAt`) and `rdi` holds the number of rounds (which the modes do not
write). `modeCoreSpec` is encryption's, for CTR.

`prepare` is ECB's key setup, inline, and leaves the number of rounds in
`rdi`; `crypt` calls `vg_camellia_crypt_prepared` (`WP.call`, with its
contract on x86-64, `cryptCallX86_64`) on the core's slots, its return address
stored in the 8 bytes below `rsp`, which the core's slots are apart from.
The data's address, the blocks left and the number of rounds cross the call
in `r12`–`r14`, which the function restores; the slots' address stays in
`sb`, where the function moves `ws`.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (sb t0 setMasks st movS movR)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion bufRegion bufAddr Layout CoreSpec modeRegs of_not_modeRegs stkRegion
  stkList coreFrame)
open VG.Proof.Camellia (schedWords schedWords_getD wordAt_frame bytesAt_eq_blockAt ofFn_toList encryptWith_eq
  decryptWith_eq dirPerm_lt specDir)
open VG.Proof.Camellia.Prepared (Holds)

/-- The number of rounds in `rsi` and the schedule at `rdi`, outside the
regions `rs`, and the 8 bytes below `rsp`, where the core's call stores its
return address, apart from `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Nat × List (BitVec 64)) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ s.gpr .rsi = BitVec.ofNat 64 k.1 ∧ (k.1 = 18 ∨ k.1 = 24) ∧
    k.2 = schedWords s.mem p k.1 ∧ (⟨p, 272⟩ : Region) ∈ s.rd ∧ p.toNat + 272 ≤ 2 ^ 64 ∧
    (∀ r ∈ rs, Region.Disjoint ⟨p, 272⟩ r) ∧
    8 ≤ (s.gpr .rsp).toNat ∧ ∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .rsp) 8) r

theorem dirCore_total (d : Dir) : (dirCore d).total = 409 := rfl

theorem stkList_dirCore (d : Dir) (rsp : Addr) : stkList (dirCore d) rsp = [stkRegion rsp 8] := rfl

/-- The masks and the table of subkeys in the order of `d`, the number of
rounds in `rdi`, and the 8 bytes below `rsp` apart from the slots. -/
def Ready (d : Dir) (s : State) (B : Addr) (k : Nat × List (BitVec 64)) : Prop :=
  (k.1 = 18 ∨ k.1 = 24) ∧ ReadyAt d k.1 s.mem B k.2 ∧ s.gpr .rdi = BitVec.ofNat 64 k.1 ∧
    8 ≤ (s.gpr .rsp).toNat ∧ Region.Disjoint (stkRegion (s.gpr .rsp) 8) ⟨B, 8 * 409⟩

/-- A word of the core's slots outside the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {dir : Dir} {B : Addr} {d : Nat} (hd : d + 8 ≤ 8 * tailSlot) {r : Region}
    (hr : Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B (by simp only [dirCore, tailSlot_eq, slots_eq] at hd ⊢; omega_arith))
  · refine Region.Disjoint.sub_right ?_ h
    exact VG.Offset.disjoint B (by simp only [dirCore, tailSlot_eq] at hd ⊢; omega_arith)
      (by simp only [tailSlot_eq] at hd; omega_arith) (by simp only [dirCore, tailSlot_eq]; omega_arith)

theorem ready_frame {d : Dir} {s s' : State} {B : Addr} {k : Nat × List (BitVec 64)} {rs : List Region}
    (h : Ready d s B k) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (bufRegion (dirCore d) B))
    (_ : Modes.X86_64.WrIn rs s s') (hg : ∀ r, r ∉ modeRegs (dirCore d) → s'.gpr r = s.gpr r) : Ready d s' B k := by
  obtain ⟨hR, ⟨hm, he⟩, hrdi, hst, hsdis⟩ := h
  obtain hR' : ∀ d, d + 8 ≤ 8 * tailSlot →
      s'.mem.readW (B + BitVec.ofNat 64 d) 64 = s.mem.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint h1 (hd r hr)) (by decide)
  obtain hg4 : k.1 / 6 ≤ 4 := by omega_arith
  obtain hsp : s'.gpr .rsp = s.gpr .rsp := hg .rsp (by simp only [modeRegs, dirCore]; decide)
  refine ⟨hR, ⟨fun kv hkv => ?_, fun i hi => (he i hi).congr fun j hj => ?_⟩, ?_, by rw [hsp]; exact hst,
    by rw [hsp]; exact hsdis⟩
  · have hk := mask_in hkv
    rw [evenSlot_eq, m3Slot_eq] at hk
    rw [← hm kv hkv]
    exact hR' (8 * kv.1) (by rw [tailSlot_eq]; omega_arith)
  · exact hR' (8 * keySlot + 64 * i + 8 * j) (by rw [keySlot_eq, tailSlot_eq]; omega_arith)
  · rw [hg .rdi (by simp only [modeRegs, dirCore]; decide), hrdi]

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Nat × List (BitVec 64)} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.rdi, .rsi, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hrsi, hR, hws, hin, hfit, hdis, hst, hsdis⟩ := h
  obtain hsp : s'.gpr .rsp = s.gpr .rsp := hr .rsp (by simp)
  refine ⟨p, by rw [hr .rdi (by simp), hp], by rw [hr .rsi (by simp), hrsi],
    hR, ?_, by rw [hrd]; exact hin, hfit, hdis, by rw [hsp]; exact hst, by rw [hsp]; exact hsdis⟩
  rw [hws]
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  obtain hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega_arith
  exact (wordAt_frame hf fun r hr => (hdis r hr).sub_left (VG.Offset.sub_base p hl)).symm

/-- A block whose head is one instruction, run from where that instruction leads. -/
theorem runBlock_head {i : Instr} {is : List Instr} {s s₁ : State} (h : runBlock isa [i] s = some s₁) :
    runBlock isa (i :: is) s = runBlock isa is s₁ := by
  rw [show i :: is = [i] ++ is from rfl, runBlock_append', h, Option.bind_some]

/-- Running from `s` with a region within its writable ones added to them. -/
theorem WP.widen_wr {c : Prog isa} {s : State} {r : Region} (hr : Covers [r] s.wr) {Q : State → Prop}
    (h : WP isa c (s.withRegions s.rd (r :: s.wr)) fun s' => Q (s'.withRegions s.rd s.wr)) : WP isa c s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  have := Exec.widen he (Covers.append (Covers.refl _) (Covers.cons hr (Covers.refl _))) (Covers.cons hr (Covers.refl _))
  simp only [State.withRegions_rd, State.withRegions_withRegions, State.withRegions_self] at this
  exact ⟨t, _, this, hq⟩

/-- The key setup, with ECB's scratch buffer among the writable regions:
the masks and the table of `rsi`'s rounds, and the rounds in `rdi`. -/
theorem prepare_core (d : Dir) {s : State} {B p : Addr} {R : Nat} (hB : s.gpr sb = B)
    (hw : (⟨B, 8 * slots⟩ : Region) ∈ s.wr) (fitB : B.toNat + 8 * slots ≤ 2 ^ 64) (hp : s.gpr .rdi = p)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 R) (hRr : R = 18 ∨ R = 24) (hin : (⟨p, 272⟩ : Region) ∈ s.rd)
    (hfit : p.toNat + 272 ≤ 2 ^ 64) (hsep : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * slots⟩) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt d R s'.mem B (schedWords s.mem p R) ∧
      s'.gpr .rdi = BitVec.ofNat 64 R ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧ Frame [⟨B, 8 * endSlot⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, -, g₁, rd₁, wr₁, f₁⟩ := setMasks_ok layerMasks hB hw
    (fun kv hkv => by
      simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
        simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot, keySlot]) (by decide)
  obtain ⟨s₂, e₂, z₂, g₂, m₂, rd₂, wr₂⟩ := cmpImmZ_ok s₁ .rsi 18
  obtain hz : s₂.zf = some (decide (R = 18)) := by
    rw [z₂, g₁ _ (by decide), hrsi, show (18 : BitVec 32).signExtend 64 = BitVec.ofNat 64 18 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
  obtain b₂ : s₂.gpr sb = B := by rw [g₂, g₁ _ (by decide), hB]
  obtain hpre : KeyPre s₂ B p := ⟨b₂, by rw [wr₂, wr₁]; exact hw, fitB,
    List.mem_append_left _ (by rw [rd₂, rd₁]; exact hin), hfit, hsep⟩
  obtain rdi₂ : s₂.gpr .rdi = p := by rw [g₂, g₁ _ (by decide), hp]
  obtain mk₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, g₂]; exact v₁ kv hkv
  show WP isa (.seq (.block (setMasks layerMasks ++ ([.alu .cmp .rsi (.imm 18)] : List Instr)))
    (.ite .e (.seq (keys d 3) (.block [.movImm64 .rdi 18])) (.seq (keys d 4) (.block [.movImm64 .rdi 24])))) s _
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some, e₂], ?_⟩)
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  obtain hg : g = 3 ∨ g = 4 := by omega_arith
  -- After the table, the rounds to `rdi`.
  obtain hmov : ∀ (v : BitVec 64), v = BitVec.ofNat 64 R → ∀ s₃, KeysPost s₂ B p g (permOf d g) s₃ →
      WP isa (.block [.movImm64 .rdi v]) s₃ fun s' => ∃ s₃, KeysPost s₂ B p g (permOf d g) s₃ ∧
        s'.mem = s₃.mem ∧ (∀ r, r ≠ .rdi → s'.gpr r = s₃.gpr r) ∧ s'.gpr .rdi = BitVec.ofNat 64 R ∧
        s'.rd = s₃.rd ∧ s'.wr = s₃.wr := fun v hv s₃ k₃ => by
    obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := movImm_ok s₃ .rdi v
    exact WP.of_runBlock ⟨s₄, e₄, s₃, k₃, m₄, o₄, by rw [r₄, hv], rd₄, wr₄⟩
  refine WP.mono (M := isa) (Q := fun s' => ∃ s₃, KeysPost s₂ B p g (permOf d g) s₃ ∧
        s'.mem = s₃.mem ∧ (∀ r, r ≠ .rdi → s'.gpr r = s₃.gpr r) ∧ s'.gpr .rdi = BitVec.ofNat 64 R ∧
        s'.rd = s₃.rd ∧ s'.wr = s₃.wr) (WP.ite (decide (R = 18)) (by simp [X86_64.eval, hz]) (fun h => ?_) (fun h => ?_))
    fun s₄ ⟨s₃, k₃, m₄, o₄, rdi₄, rd₄, wr₄⟩ => ?_
  · obtain rfl : R = 18 := of_decide_eq_true h
    obtain rfl : g = 3 := by omega_arith
    exact WP.seq (WP.mono (keys_wp d (Or.inl rfl) hpre rdi₂ mk₂) fun s₃ ⟨k₃, _⟩ => hmov _ rfl s₃ k₃)
  · have hR4 : R = 24 := by have := of_decide_eq_false h; omega_arith
    subst hR4
    obtain rfl : g = 4 := by omega_arith
    exact WP.seq (WP.mono (keys_wp d (Or.inr rfl) hpre rdi₂ mk₂) fun s₃ ⟨k₃, _⟩ => hmov _ rfl s₃ k₃)
  have b₃ : s₃.gpr sb = B := k₃.pre.base
  obtain keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → r ≠ t0 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [o₄ r h3, k₃.regs r h1 h2 h3, g₂, g₁ r h4]
  refine ⟨⟨by rw [m₄]; exact k₃.masks.at b₃, fun i hi => ?_⟩, rdi₄,
    by rw [keep sb (by decide) (by decide) (by decide) (by decide), hB],
    keep _ (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide), keep _ (by decide) (by decide) (by decide) (by decide), ?_⟩
  · rw [hgR] at hi
    have := k₃.ent i hi
    rw [m₂] at this
    obtain hp' : permOf d g i < 8 * g + 2 := dirPerm_lt (specDir d) hi
    obtain hl : permOf d g i < Spec.Camellia.scheduleLength R := by simp only [Spec.Camellia.scheduleLength]; omega_arith
    rw [keyEntry_eq, hgR, schedWords_getD _ _ hl, m₄]
    rw [wordAt_frame f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hsep.sub_left (VG.Offset.sub_base p (by simp only [Spec.Camellia.scheduleLength] at hl; omega_arith))).sub_right
        (Region.sub_prefix (by rw [keySlot_eq, slots_eq]; omega_arith))] at this
    exact this
  · have kf := k₃.frame
    rw [m₂] at kf
    rw [m₄]
    exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [keySlot_eq, endSlot_eq]; omega_arith)⟩).trans kf

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready d s' B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧
      Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hp, hrsi, hRr, hws, hin, hfit, hdis, hst, hsdis⟩ := hk
  dsimp only at hrsi hRr hws
  subst hws
  have hfB := hs.fit
  rw [dirCore_total] at hfB
  obtain hsub : Covers [⟨B, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, hs.wr, 0, by simp, by show 0 + 8 * slots ≤ 8 * (dirCore d).total; rw [dirCore_total, slots_eq]; omega_arith⟩
  obtain hsep : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * slots⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by rw [dirCore_total, slots_eq]; omega_arith))
  refine WP.widen_wr hsub (WP.mono (prepare_core d (s := s.withRegions s.rd (⟨B, 8 * slots⟩ :: s.wr)) hB
    List.mem_cons_self (by rw [slots_eq]; omega_arith) hp hrsi hRr hin hfit hsep)
    fun s' ⟨hr', rdi', b', rsp', rdx', r8', f'⟩ => ?_)
  change ReadyAt d R s'.mem B (schedWords s.mem p R) at hr'
  change s'.gpr .rsp = s.gpr .rsp at rsp'
  change Frame [⟨B, 8 * endSlot⟩] s.mem s'.mem at f'
  change Ready d s' B _ ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rdx = s.gpr .rdx ∧
    s'.gpr .r8 = s.gpr .r8 ∧ Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧ s.rd = s.rd ∧ s.wr = s.wr
  refine ⟨⟨hRr, hr', rdi', by rw [rsp']; exact hst, by rw [rsp', ← dirCore_total d]; exact hsdis _ hR⟩, b', rsp',
    rdx', r8', f'.sub fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore, endSlot_eq, slots_eq]; omega_arith)⟩

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Camellia.Subkeys → Spec.Cbc.Cipher
  | .encrypt => Spec.Camellia.cipher
  | .decrypt => Spec.Camellia.invCipher

/-- The cipher of `d` on a block in memory: the block function. -/
theorem dirCipher_bytes (d : Dir) (sk : Spec.Camellia.Subkeys) (m : Mem) (p : Addr) :
    dirCipher d sk (Spec.Aes.bytesAt m p 16) =
      (Proof.Camellia.blockFn sk (specDir d) (Spec.Camellia.blockAt m p)).toList := by
  cases d
  · rw [dirCipher, Spec.Camellia.cipher, bytesAt_eq_blockAt, ofFn_toList]; rfl
  · rw [dirCipher, Spec.Camellia.invCipher, bytesAt_eq_blockAt, ofFn_toList]; rfl

/-- The table, through memory that differs only apart from the working space. -/
theorem holds_frame {m m' : Mem} {B : Addr} {R : Nat} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    {rs : List Region} (hR : R = 18 ∨ R = 24) (h : Holds layout m B R w d) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨B, 8 * slots⟩ r) : Holds layout m' B R w d :=
  fun r hr i hi => by
    have hr' := hr
    rw [layout_table] at hr'
    obtain hi' : r.1 + i < 8 * slots := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      have : R / 6 ≤ 4 := by omega_arith
      rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_arith
    rw [hf.bytes (R := ⟨B, 8 * slots⟩) hd (by show 8 * slots ≤ 2 ^ 64; rw [slots_eq]; omega_arith) hi']
    exact h _ hr i hi

/-- The table survives what a batch keeps. -/
theorem holds_of_keeps {m m' : Mem} {B : Addr} {R : Nat} {w : List (BitVec 64)} {d : Spec.Camellia.Direction}
    (hR : R = 18 ∨ R = 24) (h : Holds layout m B R w d)
    (hk : Proof.Camellia.Prepared.Keeps B slots layout.cryptScratch m m') : Holds layout m' B R w d :=
  fun r hr i hi => by
    have hr' := hr
    rw [layout_table] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    obtain h4 : R / 6 ≤ 4 := by omega_arith
    obtain hb : r.1 + i < 8 * slots ∧ ((384 ≤ r.1 + i ∧ r.1 + i < 424) ∨ (768 ≤ r.1 + i ∧ r.1 + i < 2944)) := by
      rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega_arith
    rw [hk (r.1 + i) hb.1 (by
      simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      rw [evenSlot_eq, m3Slot_eq, keySlot_eq, endSlot_eq, savedSlot_eq, tailSlot_eq]
      omega_arith)]
    exact h _ hr i hi

/-- A block, through memory that differs only apart from it. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : Spec.Camellia.blockAt m' p = Spec.Camellia.blockAt m p := by
  simp only [Spec.Camellia.blockAt]
  congr 1
  funext j
  exact hf.bytes (R := ⟨p, 16⟩) hd (by show 16 ≤ 2 ^ 64; omega_arith) j.isLt

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Camellia.Subkeys} {d : Spec.Camellia.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Camellia.blocksAt m' D n = Spec.Camellia.ecb K d (Spec.Camellia.blocksAt m D n)) {j : Nat}
    (hj : j < n) : Spec.Camellia.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      Proof.Camellia.blockFn K d (Spec.Camellia.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  rw [Proof.Camellia.ecb_eq] at this
  simpa [Spec.Camellia.blocksAt, hj] using this

/-- A register `vg_camellia_crypt_prepared` never writes. -/
theorem crypt_keeps {r : Reg} (h : cryptPrepared.allInstrs (fun i => !Taint.clobbers i r) = true) :
    ∀ i ∈ instrs cryptPrepared, Taint.clobbers i r = false := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  exact fun i hi => by simpa using h i hi

theorem crypt_nosp : NoSp cryptPrepared := crypt_keeps (by lit_decide)

theorem crypt_depth : Code.depth cryptPrepared = 0 := rfl

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : Ready d s B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧ Ready d s' B k ∧
      Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (bufAddr (dirCore d) B j) 16 =
        dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (bufAddr (dirCore d) B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨hRr, hready, hrdi, hst, sW⟩ := hr
  dsimp only at hRr hready hrdi ⊢
  have hw := hs.wr
  have hfit := hs.fit
  simp only [dirCore_total] at hw hfit
  obtain hH : Holds layout s.mem B R ws (specDir d) := by
    refine holds_of_words ?_
    rw [ofSpecDir_specDir]
    exact words_of_readyAt hready
  show WP isa cryptCall s _
  -- The registers to keep, to `r12`–`r15`, and the arguments.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .r12 .rdx
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .r13 .r8
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .r14 .rdi
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := movR_ok s₃ .rsi sb
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := movImm_ok s₅ .rdx (BitVec.ofNat 64 slots)
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [runBlock_head e₁, runBlock_head e₂, runBlock_head e₃, runBlock_head e₅, e₆], ?_⟩)
  obtain m₆' : s₆.mem = s.mem := by rw [m₆, m₅, m₃, m₂, m₁]
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₃, rd₂, rd₁]
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₃, wr₂, wr₁]
  obtain g₆ : ∀ r, r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .rsi → r ≠ .rdx → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h5 h6 => by rw [o₆ r h6, o₅ r h5, o₃ r h3, o₂ r h2, o₁ r h1]
  obtain rsp₆ : s₆.gpr .rsp = s.gpr .rsp := g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain rdi₆ : s₆.gpr .rdi = BitVec.ofNat 64 R := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), hrdi]
  obtain rsi₆ : s₆.gpr .rsi = B := by rw [o₆ _ (by decide), r₅, o₃ _ (by decide),
    o₂ _ (by decide), o₁ _ (by decide), hB]
  have rdx₆ : s₆.gpr .rdx = BitVec.ofNat 64 slots := r₆
  obtain r12₆ : s₆.gpr .r12 = s.gpr .rdx := by
    rw [o₆ _ (by decide), o₅ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁]
  obtain r13₆ : s₆.gpr .r13 = s.gpr .r8 := by
    rw [o₆ _ (by decide), o₅ _ (by decide), o₃ _ (by decide), r₂, o₁ _ (by decide)]
  obtain r14₆ : s₆.gpr .r14 = BitVec.ofNat 64 R := by
    rw [o₆ _ (by decide), o₅ _ (by decide), r₃, o₂ _ (by decide), o₁ _ (by decide), hrdi]
  obtain hE := (s.gpr .rsp).isLt
  obtain stS : Region.Disjoint (stkRegion (s.gpr .rsp) 8) ⟨B, 8 * slots⟩ :=
    sW.sub_right (Region.sub_prefix (by rw [slots_eq]; omega_arith))
  -- The return address the call stores.
  obtain hret : Frame [stkRegion (s.gpr .rsp) 8] s₆.mem s₆.callEntry.mem := by
    rw [State.callEntry_mem, rsp₆]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega_arith) (by omega_arith))
  obtain hHE : Holds layout s₆.callEntry.mem B R ws (specDir d) :=
    holds_frame (m := s₆.mem) hRr (by rw [m₆']; exact hH) hret fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact stS.symm
  let sE := s₆.callEntry.withRegions [] [⟨B, 8 * slots⟩]
  obtain eRdi : sE.gpr .rdi = BitVec.ofNat 64 R := by
    show s₆.callEntry.gpr .rdi = _; rw [State.callEntry_gpr _ (by decide), rdi₆]
  obtain eRsi : sE.gpr .rsi = B := by
    show s₆.callEntry.gpr .rsi = B; rw [State.callEntry_gpr _ (by decide), rsi₆]
  obtain eRdx : sE.gpr .rdx = BitVec.ofNat 64 slots := by
    show s₆.callEntry.gpr .rdx = _; rw [State.callEntry_gpr _ (by decide), rdx₆]
  obtain eRsp : sE.gpr .rsp = s.gpr .rsp - 8 := by
    show s₆.callEntry.gpr .rsp = _; rw [State.callEntry_rsp, rsp₆]
  obtain tsl : (BitVec.ofNat 64 slots).toNat = slots := by rw [slots_eq]; rfl
  obtain tR : (BitVec.ofNat 64 R).toNat = R := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  obtain hsub : ∀ r ∈ ([⟨B, 8 * slots⟩] : List Region), ∃ r' ∈ s₆.wr, ∃ off,
      r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, by rw [wr₆']; exact hs.wr, 0, by simp, by
      show 0 + 8 * slots ≤ 8 * (dirCore d).total; rw [dirCore_total, slots_eq]; omega_arith⟩
  refine WP.seq (WP.call (c := cryptPrepared) (k := cryptCallX86_64) cryptCall_correct crypt_nosp
    (by rw [crypt_depth]; decide) (rd := []) (wr := [⟨B, 8 * slots⟩]) ?_ ?_ ?_ ?_)
  · change cryptX86_64.pre sE
    simp only [cryptX86_64]
    rw [eRdi, eRsi, eRdx, eRsp, tsl, tR]
    refine ⟨rfl, by rw [Nat.mul_comm]; rfl, ?_, by rw [slots_eq]; omega_arith, hRr, by rw [size_eq],
      ws, specDir d, hHE⟩
    rw [Nat.mul_comm slots 8]
    exact stS
  · exact Covers.right (Covers.of_sub hsub)
  · exact Covers.of_sub hsub
  rintro s₇ rd₇ wr₇ cs frame - ⟨s₂', mem₂, g₂', post, hsb⟩
  change cryptX86_64.post sE s₂' at post
  simp only [cryptX86_64] at post
  rw [eRdi, eRsi, eRdx, tsl, tR, mem₂] at post
  obtain ⟨hE', hK⟩ := post
  obtain hEcb := hE' ws (specDir d) hHE
  rw [crypt_depth, rsp₆, m₆'] at frame
  have frame' : Frame [⟨B, 8 * slots⟩, stkRegion (s.gpr .rsp) 8] s.mem s₇.mem := frame
  obtain hcs : ∀ r ∈ [Reg.r12, .r13, .r14, .rsp], r ∈ calleeSaved := by decide
  obtain keep₇ : ∀ r ∈ [Reg.r12, .r13, .r14, .rsp], s₇.gpr r = s₆.gpr r := fun r hr => cs r (hcs r hr)
  obtain sb₇ : s₇.gpr sb = B := by rw [← g₂' _ (by decide)]; exact hsb.trans eRsi
  -- The kept registers back.
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movR_ok s₇ .rdx .r12
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := movR_ok s₈ .r8 .r13
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := movR_ok s₉ .rdi .r14
  obtain m₁₁' : s₁₁.mem = s₇.mem := by rw [m₁₁, m₉, m₈]
  obtain rsp₁₁ : s₁₁.gpr .rsp = s.gpr .rsp := by
    rw [o₁₁ _ (by decide), o₉ _ (by decide), o₈ _ (by decide), keep₇ .rsp (by simp), rsp₆]
  refine WP.of_runBlock ⟨s₁₁, by rw [runBlock_head e₈, runBlock_head e₉, e₁₁],
    by rw [o₁₁ _ (by decide), o₉ _ (by decide), o₈ _ (by decide), sb₇], rsp₁₁,
    by rw [o₁₁ _ (by decide), o₉ _ (by decide), r₈, keep₇ .r12 (by simp), r12₆],
    by rw [o₁₁ _ (by decide), r₉, o₈ _ (by decide), keep₇ .r13 (by simp), r13₆],
    ⟨hRr, ?_, by rw [r₁₁, o₉ _ (by decide), o₈ _ (by decide), keep₇ .r14 (by simp), r14₆],
      by rw [rsp₁₁]; exact hst, by rw [rsp₁₁]; exact sW⟩, ?_, fun j hj => ?_,
    by rw [rd₁₁, rd₉, rd₈, rd₇, rd₆'], by rw [wr₁₁, wr₉, wr₈, wr₇, wr₆']⟩
  · have := readyAt_of_words (words_of_holds (holds_of_keeps hRr hHE hK))
    rw [ofSpecDir_specDir, ← m₁₁'] at this
    exact this
  · rw [m₁₁']
    refine frame'.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore]; omega_arith)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (by rw [stkList_dirCore]; exact List.mem_singleton_self _), fun _ h => h⟩
  · have hj' : j < 8 := hj
    obtain ha : bufAddr (dirCore d) B j = B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := by
      simp only [bufAddr, dirCore, layout, VG.Offset.add_add]
    obtain hblk : Spec.Camellia.blockAt sE.mem (B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j)) =
        Spec.Camellia.blockAt s.mem (B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j)) := by
      rw [← m₆']
      refine blockAt_frame hret fun r hr => ?_
      rw [List.mem_singleton] at hr; subst hr
      rw [VG.Offset.add_add]
      exact (stS.sub_right (VG.Offset.sub_base _ (by simp only [layout, tailSlot_eq, slots_eq]; omega_arith))).symm
    rw [ha, dirCipher_bytes, bytesAt_eq_blockAt, m₁₁', blockAt_of_ecb hEcb hj', hblk]

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 2 := rfl

/-- Camellia's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Nat × List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame := ready_frame
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

/-- Camellia's core for encryption, for CTR. -/
abbrev modeCoreSpec : CoreSpec modeCore := dirCoreSpec .encrypt

end VG.Proof.Camellia.X86_64
