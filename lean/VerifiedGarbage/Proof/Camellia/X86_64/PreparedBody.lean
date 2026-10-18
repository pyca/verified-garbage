module

public import VerifiedGarbage.Proof.Camellia.X86_64.Ecb
public import VerifiedGarbage.Proof.Camellia.X86_64.Crypt8
public import VerifiedGarbage.Proof.Modes.X86_64.Setup
public import VerifiedGarbage.Impl.Camellia.X86_64.Prepared
public import VerifiedGarbage.Proof.Camellia.Words
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs

/-!
# Camellia's batches under prepared subkeys on x86-64: the code

What `vg_camellia_crypt_prepared` reads (`layout`,
`Spec.Camellia.Prepared.Holds`) is the masks and the table that ECB's
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

theorem entryW_word (m : Mem) (B : Addr) (e j : Nat) :
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
  rw [entryW_word, h _ (.inr (by omega)), preparedWord_entry R w d hj]

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
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [savedSlot_eq, slots_eq]; omega) (by rw [savedSlot_eq]; omega)⟩)
    (by rw [savedSlot_eq]; omega)
  exact ⟨s', by rw [saveRegs_eq]; exact e', v', g', rd', wr', f'⟩

/-- The registers' restores read their slots. -/
theorem restore_loads {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa restoreRegs s = some s' ∧ (∀ i < 6, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 6, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e', v', o', m', rd', wr'⟩ := Proof.Modes.X86_64.loads_ok savedSlot sreg 6 s hb
    (fun i _ => sreg_ne_sb i) (by decide)
    (fun i hi => ⟨_, List.mem_append_right _ hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [savedSlot_eq, slots_eq]; omega) (by rw [savedSlot_eq]; omega)⟩)
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
  have hg : g = 3 ∨ g = 4 := by omega
  have hfit := fitB
  rw [slots_eq] at hfit
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .rsi
  have b₁ : s₁.gpr sb = b := r₁.trans hb
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂⟩ := save_saved (b := b) (by rw [wr₁]; exact hwr) b₁
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := cmpImmZ_ok s₂ .rdi 18
  have b₃ : s₃.gpr sb = b := by rw [g₃, g₂, b₁]
  have hz₃ : s₃.zf = some (decide (g = 3)) := by
    rw [z₃, show (18 : BitVec 32).signExtend 64 = BitVec.ofNat 64 18 from rfl, g₂, o₁ _ (by decide),
      show s₀.gpr .rdi = BitVec.ofNat 64 R by simp only [R, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩)
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
  · have hg4 : g = 4 := by have := of_decide_eq_false h; omega
    obtain ⟨s', e', x', o', m', rd', wr'⟩ := endAddr_ok s₃ 4
    exact WP.of_runBlock ⟨s', e', by rw [x', b₃, signExtend_end (.inr rfl), hg4], o', m', rd', wr'⟩
  have b₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), b₃]
  have hw₄ : (⟨b, 8 * slots⟩ : Region) ∈ s₄.wr := by rw [wr₄, wr₃, wr₂, wr₁]; exact hwr
  obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := stReg_ok (s := s₄) (b := b) (k := endSlot) .rdi b₄
    ⟨_, hw₄, by rw [wordAddr]; exact VG.Offset.contains_base b (by rw [endSlot_eq, slots_eq]; omega) (by rw [endSlot_eq]; omega)⟩
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a⟩ := movR_ok s₅ .rdx sb
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := addImm_ok s₆a .rdx (BitVec.ofNat 32 (8 * tailSlot))
  have b₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₆a _ (by decide), g₅, b₄]
  have rdx₆ : s₆.gpr .rdx = b + BitVec.ofNat 64 (8 * tailSlot) := by
    rw [r₆, r₆a, g₅, b₄, signExtend_tail]
  have mem₆ : s₆.mem = s₄.mem.writeW (wordAddr b endSlot) (s₄.gpr .rdi) := by rw [m₆, m₆a, m₅]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₆a, wr₅, wr₄, wr₃, wr₂, wr₁]
  have hw₆ : (⟨b, 8 * slots⟩ : Region) ∈ s₆.wr := by rw [wr₆']; exact hwr
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [show ([st endSlot .rdi] ++ tailAddr .rdx : List Instr) = [st endSlot .rdi] ++ ([movR .rdx sb] ++
      [.alu .add .rdx (.imm (BitVec.ofNat 32 (8 * tailSlot)))]) from rfl, runBlock_append', e₅, Option.bind_some,
      runBlock_append', e₆a, Option.bind_some, e₆], ?_⟩)
  -- The slots below the saved registers but the postwhitening's, unchanged.
  have slot₆ : ∀ k < savedSlot, k ≠ endSlot →
      s₆.mem.readW (wordAddr b k) 64 = s₀.mem.readW (wordAddr b k) 64 := fun k hk hne => by
    rw [mem₆, Proof.Modes.X86_64.readW_slot_write _ (by rw [savedSlot_eq] at hk; omega)
      (by rw [endSlot_eq]; omega), ite_eq_right hne, m₄, m₃, ← m₁]
    refine f₂.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact VG.Offset.disjoint b (.inl (by rw [savedSlot_eq] at hk ⊢; omega)) (by rw [savedSlot_eq] at hk; omega)
      (by rw [savedSlot_eq]; omega)
  have hcore : CorePre s₆ g (keyEntry w g d) :=
    { scr := by rw [b₆]; exact hw₆
      dat := fun k hk => ⟨_, hw₆, by
        rw [rdx₆, wordAddr, VG.Offset.add_add]
        exact VG.Offset.contains_base b (by rw [tailSlot_eq, slots_eq]; omega) (by rw [tailSlot_eq]; omega)⟩
      sep := by
        rw [rdx₆, b₆]
        exact VG.Offset.disjoint_base b (by omega) (by rw [tailSlot_eq]; omega)
      fit := by rw [b₆]; exact fitB
      fitD := by
        rw [rdx₆, VG.Offset.toNat_add_ofNat, tailSlot_eq,
          Nat.mod_eq_of_lt (show 8 * 377 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega)]
        omega
      nk34 := by omega
      masks := fun kv hkv => by
        show s₆.mem.readW (wordAddr (s₆.gpr sb) kv.1) 64 = kv.2
        have hk := mask_in hkv
        rw [evenSlot_eq, m3Slot_eq] at hk
        rw [b₆, slot₆ _ (by rw [savedSlot_eq]; omega) (by rw [endSlot_eq]; omega)]
        exact hr.1 kv hkv
      keys := fun i hi => by
        have := hr.2 i (by rw [hgR]; exact hi)
        rw [hgR] at this
        refine this.congr fun j hj => ?_
        rw [b₆, entryW_word, entryW_word, slot₆ _ (by rw [keySlot_eq, savedSlot_eq]; omega)
          (by rw [keySlot_eq, endSlot_eq]; omega)]
      hg := hg
      bound := by
        show s₆.mem.readW (wordAddr (s₆.gpr sb) endSlot) 64 = _
        rw [b₆, mem₆, Proof.Modes.X86_64.readW_slot_write _ (by rw [endSlot_eq]; omega)
          (by rw [endSlot_eq]; omega), ite_eq_left rfl, rdi₄] }
  refine WP.seq (WP.mono (crypt8_ok hcore) fun s₇ ⟨c₇, o₇⟩ => ?_)
  have base₇ : s₇.gpr sb = b := by rw [c₇.base, b₆]
  have f₇ : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩] s₆.mem s₇.mem := by
    have := c₇.frame; rw [b₆, rdx₆] at this; exact this
  have dis₇ : ∀ k, keySlot ≤ k → k < tailSlot → ∀ r ∈ [(⟨b, 8 * keySlot⟩ : Region),
      ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩], Region.Disjoint ⟨wordAddr b k, 8⟩ r := fun k h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [wordAddr]
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by omega) (by rw [tailSlot_eq] at h2; omega)
    · exact VG.Offset.disjoint b (.inl (by omega)) (by rw [tailSlot_eq] at h2; omega) (by rw [tailSlot_eq]; omega)
  have sv₇ : Saved s₁ b s₇.mem := fun i hi => by
    rw [← sv₂ i hi]
    rw [f₇.readW (Region.contains_self _ _) (dis₇ _ (by rw [keySlot_eq, savedSlot_eq]; omega)
      (by rw [savedSlot_eq, tailSlot_eq]; omega)) (by decide), mem₆,
      Proof.Modes.X86_64.readW_slot_write _ (by rw [savedSlot_eq]; omega) (by rw [endSlot_eq]; omega),
      ite_eq_right (by rw [savedSlot_eq, endSlot_eq]; omega), m₄, m₃]
  obtain ⟨s₈, e₈, rg₈, og₈, m₈, rd₈, wr₈⟩ := restore_loads (by rw [c₇.wr]; exact hw₆) base₇ sv₇
  have hk7 : ∀ k, keySlot ≤ k → k < savedSlot → k ≠ endSlot →
      s₇.mem.readW (wordAddr b k) 64 = s₀.mem.readW (wordAddr b k) 64 := fun k h1 h2 h3 => by
    rw [← slot₆ k h2 h3]
    exact f₇.readW (Region.contains_self _ _) (dis₇ k h1 (by rw [savedSlot_eq, tailSlot_eq] at *; omega)) (by decide)
  have rsp₈ : s₈.gpr .rsp = s₀.gpr .rsp := by
    rw [og₈ _ (fun i _ => by unfold sreg; split <;> decide), c₇.keep _ (by decide) (by decide) (by decide),
      o₆ _ (by decide), o₆a _ (by decide), g₅, o₄ _ (by decide), g₃, g₂, o₁ _ (by decide)]
  refine WP.of_runBlock ⟨s₈, e₈, fun i hi => by rw [rg₈ i hi, o₁ _ (sreg_ne_sb i)], rsp₈,
    by rw [og₈ _ (fun i _ => (sreg_ne_sb i).symm), base₇], ?_, ?_,
    by rw [rd₈, c₇.rd, rd₆, rd₆a, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₈, c₇.wr, wr₆'], fun j hj => ?_⟩
  · refine ⟨fun kv hkv => by rw [m₈]; exact c₇.masks.at base₇ kv hkv, fun i hi => (hr.2 i hi).congr fun j hj => ?_⟩
    have hg4 : (s₀.gpr .rdi).toNat / 6 ≤ 4 := by omega
    rw [entryW_word, entryW_word, m₈, hk7 _ (by omega) (by rw [keySlot_eq, savedSlot_eq]; omega)
      (by rw [keySlot_eq, endSlot_eq]; omega)]
  · rw [m₈]
    have l₆ : Frame [⟨b, 8 * keySlot⟩, ⟨wordAddr b endSlot, 8⟩, ⟨wordAddr b savedSlot, 8 * (tailSlot + 16 - savedSlot)⟩]
        s₀.mem s₆.mem := by
      have f₂' : Frame [⟨wordAddr b savedSlot, 8 * (tailSlot + 16 - savedSlot)⟩] s₀.mem s₄.mem := by
        rw [m₄, m₃, ← m₁]
        exact f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr; subst hr; rw [wordAddr]
          exact VG.Offset.sub b (Nat.le_refl _) (by rw [savedSlot_eq, tailSlot_eq]; omega)⟩
      have fw : Frame [⟨wordAddr b endSlot, 8⟩] s₄.mem s₆.mem := by
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
        exact VG.Offset.sub b (by rw [savedSlot_eq, tailSlot_eq] <;> omega) (by rw [savedSlot_eq, tailSlot_eq] <;> omega))
  · have := o₇ j hj
    simp only [blk, c₇.rdx, rdx₆] at this
    rw [m₈, show b + BitVec.ofNat 64 (8 * tailSlot + 16 * j) = b + BitVec.ofNat 64 (8 * tailSlot) +
      BitVec.ofNat 64 (16 * j) by rw [VG.Offset.add_add], this, ← hgR, crypt_spec d hR]
    refine congrArg _ (Vector.ext fun i hi => ?_)
    simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn]
    rw [show b + BitVec.ofNat 64 (8 * tailSlot) + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 i =
      b + BitVec.ofNat 64 (8 * tailSlot) + BitVec.ofNat 64 (16 * j + i) by
        simp only [VG.Offset.add_add, Nat.add_assoc]]
    have hdis : ∀ r ∈ ([⟨wordAddr b endSlot, 8⟩] : List Region),
        Region.Disjoint ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩ r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [wordAddr]
      exact VG.Offset.disjoint b (.inr (by rw [endSlot_eq, tailSlot_eq]; omega)) (by rw [tailSlot_eq]; omega)
        (by rw [endSlot_eq]; omega)
    rw [mem₆, (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (⟨wordAddr b endSlot, 8⟩ : Region)) _
        (Region.contains_self _ _)).bytes hdis (by show (128 : Nat) ≤ 2 ^ 64; decide)
        (by show 16 * j + i < 128; omega), m₄, m₃, ← m₁]
    refine f₂.bytes (R := ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩) (fun r hr => ?_)
      (by show (128 : Nat) ≤ 2 ^ 64; decide) (by show 16 * j + i < 128; omega)
    simp only [List.mem_singleton] at hr; subst hr
    rw [wordAddr]
    exact VG.Offset.disjoint b (.inr (by rw [savedSlot_eq, tailSlot_eq] <;> omega)) (by rw [tailSlot_eq] <;> omega)
      (by rw [savedSlot_eq]; omega)

end VG.Proof.Camellia.X86_64
