module

public import VerifiedGarbage.Proof.Modes.RISCV64.Core
public import VerifiedGarbage.Impl.Camellia.RISCV64.Modes
public import VerifiedGarbage.Spec.Camellia.Cbc
public import VerifiedGarbage.Proof.Camellia.RISCV64.Ecb
import VerifiedGarbage.Proof.Camellia.RISCV64.Crypt8
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Camellia.Words
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Camellia.RISCV64.Fl
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-!
# Camellia's core for the modes on RISC-V

`dirCoreSpec d R`: Camellia's core for the direction `d` and `R` rounds
(`Impl.Camellia.RISCV64.dirCore d R`) meets what the modes need of a core
(`Proof.Modes.RISCV64.CoreSpec`), with the key the schedule's words, its
cipher `Spec.Camellia.cipher` under the subkeys of `R` rounds of them for
encryption and `Spec.Camellia.invCipher` for decryption, as on PPC64LE
(`Proof/Camellia/PPC64LE/ModeCore.lean`). The key's argument is the
schedule at `a0` (`KeyArgs`); it is ready when the masks and the table of
subkeys in `d`'s order are in ECB's scratch buffer, the core's slots from
`ecbOff` (`Ready`, `ReadyAt`).

Both pieces run from the state narrowed to the schedule and ECB's scratch
buffer (`WP.narrow`), as ECB's own proofs state it: the modes' state parked
(`park_ok`), ECB's prologue (`prologue_ok`) and key setup (`keys_wp`), or
the registers saved (`save_ok`) and the eight blocks (`crypt8_ok`), then
the registers restored (`restore_ok`) and the modes' state back
(`unpark_ok`).
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64.Mode

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Straight VG.Impl.Camellia.RISCV64 VG.Proof.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (sb t0 t1 kp movR)
open VG.Proof.Aes.RISCV64 (sboxWrites)
open VG.Proof.Modes.RISCV64 (coreRegion blkRegion blkAddr slotA CoreSpec Layout ScrIn kept KeptBut)
open VG.Proof.Camellia (HalfRel schedWords schedWords_getD wordAt_frame dirPerm_lt blockFn bytesAt_eq_blockAt
  ofFn_toList)

/-! ## The addresses -/

/-- ECB's scratch buffer in the frame at `B`, and the slots of `ra` and `a0`. -/
abbrev ecbA (B : Addr) : Addr := B + BitVec.ofNat 64 ecbOff
abbrev raA (B : Addr) : Addr := ecbA B + BitVec.ofNat 64 (8 * raSlot)
abbrev a0A (B : Addr) : Addr := ecbA B + BitVec.ofNat 64 (8 * a0Slot)

theorem ecbOff_eq : ecbOff = 48 := rfl
theorem raSlot_eq : raSlot = 92 := rfl
theorem a0Slot_eq : a0Slot = 93 := rfl

/-! ## Parking the modes' state -/

/-- `park`: ECB's base to `t0`, `ra` and `a0` to their slots, and the modes'
`s1`–`s3` to `a2`, `a3` and `ra`. -/
theorem park_ok {s : State} {B : Addr} (hB : s.gpr Impl.Modes.RISCV64.sb = B) (hal : (ecbA B).toNat % 8 = 0)
    (hw : (⟨ecbA B, 8 * slots⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa park s = some s' ∧ s'.gpr .t0 = ecbA B ∧ s'.gpr .a2 = s.gpr .s1 ∧
      s'.gpr .a3 = s.gpr .s2 ∧ s'.gpr .ra = s.gpr .s3 ∧
      (∀ r, r ≠ .t0 → r ≠ .a2 → r ≠ .a3 → r ≠ .ra → s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW (raA B) (s.gpr .ra)).writeW (a0A B) (s.gpr .a0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [slots_eq] at hw
  refine WP.runBlock_of ?_
  rw [park]
  refine wp_addi (by decide) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr Impl.Modes.RISCV64.sb = B := by rw [u₁.other _ (by decide), hB]
  refine wp_sd (a := raA B) (by decide) (by rw [b₁, raA, ecbA, VG.Offset.add_add])
    (Spill.al8 hal (by decide))
    (by rw [u₁.wr]; exact ⟨_, hw, VG.Offset.contains_base _ (by decide) (by decide)⟩) fun s₂ m₂ => ?_
  refine wp_sd (a := a0A B) (by decide) (by rw [m₂.gpr, b₁, a0A, ecbA, VG.Offset.add_add])
    (Spill.al8 hal (by decide))
    (by rw [m₂.wr, u₁.wr]; exact ⟨_, hw, VG.Offset.contains_base _ (by decide) (by decide)⟩) fun s₃ m₃ => ?_
  simp only [movR]
  refine wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have g₃ : ∀ r, r ≠ .t0 → s₃.gpr r = s.gpr r := fun r h => by rw [m₃.gpr, m₂.gpr, u₁.other r h]
  refine ⟨?_, ?_, ?_, ?_, fun r h0 h2 h3 hra => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), m₃.gpr, m₂.gpr]
    exact u₁.gpr.trans (by rw [hB])
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃ _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃ _ (by decide)]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide)]
  · rw [u₆.other r hra, u₅.other r h3, u₄.other r h2, g₃ r h0]
  · rw [u₆.mem, u₅.mem, u₄.mem, m₃.mem, m₂.gpr, m₂.mem, u₁.mem, u₁.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₆.rd, u₅.rd, u₄.rd, m₃.rd, m₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, m₃.wr, m₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, m₃.sp, m₂.sp, u₁.sp]

/-- `unpark`: the modes' state back from `a2`, `a3` and `ra`, the frame's
base from ECB's, and `ra` and `a0` from their slots. -/
theorem unpark_ok {s : State} {B : Addr} (hb : s.gpr sb = ecbA B) (hal : (ecbA B).toNat % 8 = 0)
    (hw : (⟨ecbA B, 8 * slots⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa unpark s = some s' ∧ s'.gpr .s1 = s.gpr .a2 ∧ s'.gpr .s2 = s.gpr .a3 ∧
      s'.gpr .s3 = s.gpr .ra ∧ s'.gpr .s4 = B ∧ s'.gpr .ra = s.mem.readW (raA B) 64 ∧
      s'.gpr .a0 = s.mem.readW (a0A B) 64 ∧
      (∀ r, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → r ≠ .ra → r ≠ .a0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [slots_eq] at hw
  refine WP.runBlock_of ?_
  rw [unpark]
  simp only [movR]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_subi (by decide) fun s₄ u₄ => ?_
  have g₃ : ∀ r, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s₃.gpr r = s.gpr r := fun r a b c => by
    rw [u₃.other r c, u₂.other r b, u₁.other r a]
  have b₄ : s₄.gpr sb = ecbA B := by rw [u₄.other _ (by decide), g₃ _ (by decide) (by decide) (by decide), hb]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have inR : ∀ k, 8 * k + 8 ≤ 8 * 400 → InRegions (s₄.rd ++ s₄.wr) (ecbA B + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k hk => by
      rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
      exact ⟨_, List.mem_append_right _ hw, VG.Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_ld (a := raA B) (by decide) (by rw [b₄]) (Spill.al8 hal (by decide)) (inR _ (by decide))
    fun s₅ u₅ => ?_
  refine wp_ld (a := a0A B) (by decide) (by rw [u₅.other _ (by decide), b₄]) (Spill.al8 hal (by decide))
    (by rw [u₅.rd, u₅.wr]; exact inR _ (by decide)) fun s₆ u₆ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 hra ha0 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide)]
    refine u₄.gpr.trans ?_
    rw [g₃ _ (by decide) (by decide) (by decide), hb, ecbA, BitVec.add_sub_cancel]
  · rw [u₆.other _ (by decide), u₅.gpr, m₄]
  · rw [u₆.gpr, u₅.mem, m₄]
  · rw [u₆.other r ha0, u₅.other r hra, u₄.other r h4, g₃ r h1 h2 h3]
  · rw [u₆.mem, u₅.mem, m₄]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ## The key -/

/-- The masks and the table of the subkeys of `R` rounds of the words `w`,
in the order of `d`, in ECB's scratch buffer at `b`: what the rounds read. -/
def ReadyAt (d : Dir) (R : Nat) (m : Mem) (b : Addr) (w : List (BitVec 64)) : Prop :=
  MasksAt m b ∧ ∀ i < 8 * (R / 6) + 2, EntryOk m b i (w.getD (permOf d (R / 6) i) 0)

/-- The schedule at `a0`, whose words for `R` rounds are `w`, readable and
apart from the regions `rs`. -/
def KeyArgs (R : Nat) (s : State) (rs : List Region) (w : List (BitVec 64)) : Prop :=
  ∃ p : Addr, s.gpr .a0 = p ∧ w = schedWords s.mem p R ∧ (⟨p, 272⟩ : Region) ∈ s.rd ∧
    p.toNat + 272 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 272⟩ r

/-- The table of the words `w` in the order of `d`, in the frame at `B`. -/
def Ready (d : Dir) (R : Nat) (s : State) (B : Addr) (_ : List Region) (w : List (BitVec 64)) : Prop :=
  ReadyAt d R s.mem (ecbA B) w

theorem entryW_word (m : Mem) (b : Addr) (i j : Nat) :
    entryW m b i j = m.readW (wordAddr b (keySlot + 8 * i + j)) 64 := by
  simp only [entryW, wordAddr]
  rw [show 8 * (keySlot + 8 * i + j) = 8 * keySlot + 64 * i + 8 * j by omega]

/-- The table survives what keeps the words of the masks and the table. -/
theorem readyAt_congr {d : Dir} {R : Nat} {m m' : Mem} {b : Addr} {w : List (BitVec 64)} (hR : R = 18 ∨ R = 24)
    (h : ReadyAt d R m b w)
    (hw : ∀ k, (48 ≤ k ∧ k < 59) ∨ (keySlot ≤ k ∧ k < slots) →
      m'.readW (wordAddr b k) 64 = m.readW (wordAddr b k) 64) :
    ReadyAt d R m' b w := by
  obtain ⟨hm, he⟩ := h
  have hg4 : R / 6 ≤ 4 := by omega
  refine ⟨fun kv hkv => ?_, fun i hi => (he i hi).congr fun j hj => ?_⟩
  · rw [← hm kv hkv]; exact hw _ (.inl (allMasks_range kv hkv))
  · rw [entryW_word, entryW_word]
    exact hw _ (.inr ⟨by omega, by rw [keySlot_eq, slots_eq]; rw [keySlot_eq] at *; omega⟩)

/-- A word of ECB's masks or table is apart from what writes outside the
core's slots or within its buffer. -/
theorem word_disjoint {d : Dir} {R : Nat} {B : Addr} {k : Nat} (hk : (48 ≤ k ∧ k < 59) ∨ (keySlot ≤ k ∧ k < slots))
    {r : Region}
    (hr : Region.Disjoint (coreRegion (dirCore d R) B) r ∨ Region.Sub r (blkRegion (dirCore d R) B)) :
    Region.Disjoint ⟨wordAddr (ecbA B) k, 8⟩ r := by
  have hk' : k < 400 := by rw [keySlot_eq, slots_eq] at hk; omega
  rcases hr with h | h
  · refine h.sub_left ?_
    show Region.Sub ⟨B + BitVec.ofNat 64 48 + BitVec.ofNat 64 (8 * k), 8⟩ ⟨B + BitVec.ofNat 64 48, 3200⟩
    exact VG.Offset.sub_base _ (by omega)
  · refine Region.Disjoint.sub_right ?_ h
    show Region.Disjoint ⟨B + BitVec.ofNat 64 48 + BitVec.ofNat 64 (8 * k), 8⟩
      ⟨B + BitVec.ofNat 64 (8 * 102), 4 * 4 * 1⟩
    rw [VG.Offset.add_add]
    exact VG.Offset.disjoint B (by rw [keySlot_eq] at hk; omega) (by omega) (by omega)

theorem ready_frame {d : Dir} {R : Nat} (hR : R = 18 ∨ R = 24) {s s' : State} {B : Addr} {ws : List Region}
    {w : List (BitVec 64)} {rs : List Region} (h : Ready d R s B ws w) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d R) B) r ∨ Region.Sub r (blkRegion (dirCore d R) B)) :
    Ready d R s' B ws w :=
  readyAt_congr hR h fun k hk =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint hk (hd r hr)) (by decide)

theorem keyArgs_congr {R : Nat} {s s' : State} {rs : List Region} {w : List (BitVec 64)} (h : KeyArgs R s rs w)
    (ha : s'.gpr .a0 = s.gpr .a0) (hrd : s'.rd = s.rd) (hf : Frame rs s.mem s'.mem) (hR : R = 18 ∨ R = 24) :
    KeyArgs R s' rs w := by
  obtain ⟨p, hp, hws, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [ha, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hws]
  simp only [schedWords]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have hl : 8 * i + 8 ≤ 272 := by simp only [Spec.Camellia.scheduleLength] at hi; omega
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

/-- The rounds with the subkeys in the order of `d` are its block function. -/
theorem crypt_spec (d : Dir) {R : Nat} (hR : R = 18 ∨ R = 24) (w : List (BitVec 64)) (blk : Spec.Camellia.Block) :
    Spec.Camellia.encodeBlock (Proof.Camellia.cryptWords (R / 6) (fun i => w.getD (permOf d (R / 6) i) 0)
        (Spec.Camellia.decodeBlock blk)) =
      blockFn (Spec.Camellia.subkeysOfWords R w) (specDir d) blk := by
  cases d
  · simp only [blockFn, specDir, Spec.Camellia.encryptBlock, Proof.Camellia.encryptWith_eq hR, permOf,
      Proof.Camellia.dirPerm]
  · simp only [blockFn, specDir, Spec.Camellia.decryptBlock, Proof.Camellia.decryptWith_eq hR, permOf,
      Proof.Camellia.dirPerm]

/-! ## Memory around the parked values -/

theorem slotsOf {B : Addr} {i : Nat} (hi : i < 2) :
    Region.Sub ⟨ecbA B + BitVec.ofNat 64 (8 * (raSlot + i)), 8⟩ ⟨ecbA B, 8 * slots⟩ :=
  VG.Offset.sub_base _ (by rw [raSlot_eq, slots_eq]; omega)

/-- What `park` writes keeps everything else. -/
theorem park_frame (m : Mem) (B : Addr) (v₁ v₂ : BitVec 64) :
    Frame [⟨raA B, 16⟩] m ((m.writeW (raA B) v₁).writeW (a0A B) v₂) := by
  have h₁ : (⟨raA B, 16⟩ : Region).Contains (raA B) (64 / 8) := by simp [Region.Contains]
  have h₂ : (⟨raA B, 16⟩ : Region).Contains (a0A B) (64 / 8) := by
    rw [show a0A B = raA B + BitVec.ofNat 64 8 by rw [raA, VG.Offset.add_add]; rfl]
    exact VG.Offset.contains_base _ (by decide) (by decide)
  exact ((Frame.refl _ _).writeW List.mem_cons_self _ h₁).writeW List.mem_cons_self _ h₂

/-- `park`'s slots read back what it wrote. -/
theorem park_read (m : Mem) (B : Addr) (v₁ v₂ : BitVec 64) :
    ((m.writeW (raA B) v₁).writeW (a0A B) v₂).readW (raA B) 64 = v₁ ∧
      ((m.writeW (raA B) v₁).writeW (a0A B) v₂).readW (a0A B) 64 = v₂ := by
  refine ⟨?_, Mem.readW_writeW_self64 _ _ _⟩
  have f : Frame [⟨a0A B, 8⟩] (m.writeW (raA B) v₁) ((m.writeW (raA B) v₁).writeW (a0A B) v₂) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  rw [f.readW (r := ⟨raA B, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide), Mem.readW_writeW_self64]
  simp only [List.mem_singleton] at hr; subst hr
  exact VG.Offset.disjoint (ecbA B) (.inl (by decide)) (by decide) (by decide)

/-- A word at slot `k` of ECB's scratch buffer, outside what the key setup
writes, its prologue's saves and `park`'s slots. -/
theorem word_out (b : Addr) {k : Nat} (hk : savedSlot + 14 ≤ k ∧ k < keySlot) :
    ∀ r ∈ keyRegions b ++ [⟨b, 8 * savedSlot⟩, savedRegion b], Region.Disjoint ⟨b + BitVec.ofNat 64 (8 * k), 8⟩ r := by
  rw [savedSlot_eq, keySlot_eq] at hk
  intro r hr
  simp only [keyRegions, savedRegion, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl | rfl
  · exact VG.Offset.disjoint_base b (by rw [savedSlot_eq]; omega) (by omega)
  · exact VG.Offset.disjoint b (.inl (by rw [keySlot_eq]; omega)) (by omega) (by rw [keySlot_eq, slots_eq]; decide)
  · exact VG.Offset.disjoint_base b (by rw [savedSlot_eq]; omega) (by omega)
  · exact VG.Offset.disjoint b (.inr (by rw [savedSlot_eq]; omega)) (by omega) (by rw [savedSlot_eq]; decide)

/-! ## The key setup -/

theorem a0_ne_sreg : ∀ i < 12, Reg.a0 ≠ sreg i := by decide
theorem ra_ne_sreg : ∀ i < 12, Reg.ra ≠ sreg i := by decide
theorem a2_ne_sreg : ∀ i < 12, Reg.a2 ≠ sreg i := by decide
theorem a3_ne_sreg : ∀ i < 12, Reg.a3 ≠ sreg i := by decide
theorem a5_ne_sreg : ∀ i < 12, Reg.a5 ≠ sreg i := by decide

/-- The values the core keeps: the parked ones, the frame's base, `a0` and
`ra` from their slots, and the registers `s'` restored from `s₀`. -/
theorem kept_of {s s₀ s₄ s' : State} {B : Addr} (hB : s.gpr Impl.Modes.RISCV64.sb = B)
    (a2 : s₄.gpr .a2 = s.gpr .s1) (a3 : s₄.gpr .a3 = s.gpr .s2) (ra : s₄.gpr .ra = s.gpr .s3)
    (r₀ : ∀ r, r ∈ preserved → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s₀.gpr r = s.gpr r)
    (s1 : s'.gpr .s1 = s₄.gpr .a2) (s2 : s'.gpr .s2 = s₄.gpr .a3) (s3 : s'.gpr .s3 = s₄.gpr .ra)
    (s4 : s'.gpr .s4 = B) (ra' : s'.gpr .ra = s.gpr .ra) (a0' : s'.gpr .a0 = s.gpr .a0)
    (rest : ∀ i < 12, sreg i ≠ .s1 → sreg i ≠ .s2 → sreg i ≠ .s3 → sreg i ≠ .s4 →
      s'.gpr (sreg i) = s₀.gpr (sreg i)) :
    ∀ r ∈ kept, s'.gpr r = s.gpr r := by
  intro r hr
  simp only [kept, preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  have gen : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s'.gpr r = s.gpr r :=
    fun r hp h1 h2 h3 h4 => by
      obtain ⟨i, hi, rfl⟩ := preserved_sreg r hp
      rw [rest i hi h1 h2 h3 h4, r₀ _ hp h1 h2 h3 h4]
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact a0'
  · exact ra'
  · exact gen _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [s1, a2]
  · rw [s2, a3]
  · rw [s3, ra]
  · rw [s4]; exact hB.symm
  all_goals exact gen _ (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The key setup, with ECB's scratch buffer in the frame at `B` writable
and the schedule at `p` readable. -/
theorem prepBody_wp (d : Dir) {R : Nat} (hR : R = 18 ∨ R = 24) {s : State} {B p : Addr}
    (hB : s.gpr Impl.Modes.RISCV64.sb = B) (hal : (ecbA B).toNat % 8 = 0)
    (hw : (⟨ecbA B, 8 * slots⟩ : Region) ∈ s.wr) (hfit : (ecbA B).toNat + 8 * slots ≤ 2 ^ 64)
    (hp : s.gpr .a0 = p) (hrK : (⟨p, 272⟩ : Region) ∈ s.rd) (fitK : p.toNat + 272 ≤ 2 ^ 64)
    (dSS : Region.Disjoint ⟨p, 272⟩ ⟨ecbA B, 8 * slots⟩) :
    WP isa (prepareKeys d R) s fun s' => s'.gpr Impl.Modes.RISCV64.sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      ReadyAt d R s'.mem (ecbA B) (schedWords s.mem p R) ∧ Frame [⟨ecbA B, 8 * slots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  generalize hb : ecbA B = b at hal hw hfit dSS
  obtain ⟨s₁, e₁, t0₁, a2₁, a3₁, ra₁, o₁, m₁, rd₁, wr₁, -⟩ := park_ok hB (hb ▸ hal) (hb ▸ hw)
  obtain ⟨s₂, e₂, a1₂, o₂, m₂, rd₂, wr₂⟩ := li_ok s₁ .a1 (v := R) (by omega)
  obtain ⟨s₃, e₃, b₃, g₃, sv₃, mk₃, t₃, f₃, rd₃, wr₃⟩ := prologue_ok (a := t0) (b := b)
    (by rw [o₂ _ (by decide)]; exact t0₁.trans hb) (by rw [wr₂, wr₁]; exact hw) hal
  unfold prepareKeys
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    rw [runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃], ?_⟩)
  have hk₃ : KeyPre s₃ b p := ⟨b₃, by rw [wr₃, wr₂, wr₁]; exact hw, hal, hfit,
    List.mem_append_left _ (by rw [rd₃, rd₂, rd₁]; exact hrK), fitK, dSS⟩
  have a0₃ : s₃.gpr .a0 = p := by
    rw [g₃ _ (by decide) (by decide) (by decide), o₂ _ (by decide),
      o₁ _ (by decide) (by decide) (by decide) (by decide), hp]
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  have hz : isa.eval (.zero t0) s₃ = some (decide (g = 3)) := by
    rw [Steps.eval_zero, t₃, a1₂, VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩)
  refine WP.seq (WP.mono (keys_wp d hg hz hk₃ a0₃ mk₃) fun s₄ ⟨k₄, _⟩ => ?_)
  have base₄ : s₄.gpr sb = b := k₄.pre.base
  have sv₄ : Saved s₂ b s₄.mem := fun i hi => by
    rw [← sv₃ i hi]
    refine k₄.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [keyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by omega) (by rw [savedSlot_eq]; omega)
    · exact VG.Offset.disjoint b (by rw [savedSlot_eq, keySlot_eq]; omega) (by rw [savedSlot_eq]; omega)
        (by decide)
  have hw₄ : (⟨b, 8 * slots⟩ : Region) ∈ s₄.wr := by rw [k₄.wr, wr₃, wr₂, wr₁]; exact hw
  obtain ⟨s₅, e₅, rg₅, ro₅, m₅, rd₅, wr₅⟩ := restore_ok hw₄ base₄ hal sv₄
  have b₅ : s₅.gpr sb = ecbA B := (ro₅ sb a5_ne_sreg).trans (base₄.trans hb.symm)
  obtain ⟨s₆, e₆, s1₆, s2₆, s3₆, s4₆, ra₆, a0₆, o₆, m₆, rd₆, wr₆, -⟩ :=
    unpark_ok b₅ (hb ▸ hal) (by rw [wr₅, hb]; exact hw₄)
  refine WP.of_runBlock ⟨s₆, by rw [runBlock_append', e₅, Option.bind_some, e₆], ?_⟩
  -- The memory.
  have F₁ : Frame [⟨b, 8 * slots⟩] s.mem s₂.mem := by
    rw [m₂, m₁]
    refine (park_frame _ _ _ _).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by rw [raA, hb]; exact VG.Offset.sub_base b (by rw [slots_eq]; decide)⟩
  have F₃ : Frame [⟨b, 8 * slots⟩] s₂.mem s₃.mem := f₃.sub fun r hr => by
    simp only [savedRegion, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, VG.Offset.sub_base b (by decide)⟩
  have F₄ : Frame [⟨b, 8 * slots⟩] s₃.mem s₄.mem := k₄.frame.sub fun r hr => by
    simp only [keyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, VG.Offset.sub_base b (by decide)⟩
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  -- `park`'s slots, through the prologue and the key setup.
  have slot : ∀ k, savedSlot + 14 ≤ k + 2 → k < savedSlot + 14 →
      s₄.mem.readW (b + BitVec.ofNat 64 (8 * k)) 64 = s₂.mem.readW (b + BitVec.ofNat 64 (8 * k)) 64 := by
    intro k h1 h2
    have hk : savedSlot + 12 ≤ k := by omega
    rw [k₄.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide),
      f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · simp only [savedRegion, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [savedSlot_eq] at hk h2
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint_base b (by rw [savedSlot_eq]; omega) (by omega)
      · exact VG.Offset.disjoint b (.inr (by rw [savedSlot_eq]; omega)) (by omega) (by rw [savedSlot_eq]; decide)
    · simp only [keyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [savedSlot_eq] at hk h2
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint_base b (by rw [savedSlot_eq]; omega) (by omega)
      · exact VG.Offset.disjoint b (.inl (by rw [keySlot_eq]; omega)) (by omega) (by rw [keySlot_eq, slots_eq]; decide)
  have pr := park_read s.mem B (s.gpr .ra) (s.gpr .a0)
  rw [← m₁, ← m₂] at pr
  have hra : s₄.mem.readW (raA B) 64 = s.gpr .ra := by
    rw [raA, hb, slot raSlot (by decide) (by decide), ← hb]; exact pr.1
  have ha0 : s₄.mem.readW (a0A B) 64 = s.gpr .a0 := by
    rw [a0A, hb, slot a0Slot (by decide) (by decide), ← hb]; exact pr.2
  -- The registers.
  have r₄ : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → r ≠ .a4 → r ≠ sb → r ≠ t0 → r ≠ t1 → r ≠ .a1 →
      s₄.gpr r = s₁.gpr r := fun r a b c e f g h i => by
    rw [k₄.regs r a b c e, g₃ r f g h, o₂ r i]
  refine ⟨s4₆, kept_of hB (s₄ := s₄) (s₀ := s₂)
      (by rw [r₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact a2₁)
      (by rw [r₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact a3₁)
      (by rw [r₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact ra₁)
      (fun r hr h1 h2 h3 h4 => by
        have : r ≠ .a1 ∧ r ≠ .t0 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .ra := by
          simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [o₂ r this.1, o₁ r this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2])
      (by rw [s1₆, ro₅ _ a2_ne_sreg]) (by rw [s2₆, ro₅ _ a3_ne_sreg]) (by rw [s3₆, ro₅ _ ra_ne_sreg]) s4₆
      (by rw [ra₆, m₅]; exact hra) (by rw [a0₆, m₅]; exact ha0)
      (fun i hi h1 h2 h3 h4 => by
        rw [o₆ _ h1 h2 h3 h4 (fun h => ra_ne_sreg i hi h.symm) (fun h => a0_ne_sreg i hi h.symm), rg₅ i hi]),
    ⟨?_, fun i hi => ?_⟩, ?_, by rw [rd₆, rd₅, k₄.rd, rd₃, rd₂, rd₁], by rw [wr₆, wr₅, k₄.wr, wr₃, wr₂, wr₁]⟩
  · rw [mem₆]; exact k₄.masks.at base₄
  · rw [mem₆]
    rw [hgR] at hi ⊢
    have hl : permOf d g i < Spec.Camellia.scheduleLength R := by
      have := dirPerm_lt (specDir d) hi
      simp only [Spec.Camellia.scheduleLength]; simp only [permOf] at *; omega
    have := k₄.ent i hi
    rw [schedWords_getD _ _ hl]
    rw [wordAt_frame (F₁.trans F₃) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dSS.sub_left (VG.Offset.sub_base p (by simp only [Spec.Camellia.scheduleLength] at hl; omega))] at this
    exact this
  · rw [mem₆]; exact (F₁.trans F₃).trans F₄

/-! ## The eight blocks -/

/-- `a4 := ` the address of the postwhitening's entry for `g` groups. -/
theorem endAddr_ok (s : State) {g : Nat} (hg : 1 ≤ g ∧ g ≤ 4) :
    ∃ s', runBlock isa (endAddr g) s = some s' ∧
      s'.gpr .a4 = s.gpr sb + BitVec.ofNat 64 (8 * keySlot + 512 * g) ∧
      (∀ r, r ≠ .a4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, a4₁, o₁, m₁, rd₁, wr₁⟩ := addIc_ok s .a4 sb (8 * keySlot + 512) (by decide)
  obtain ⟨s₂, e₂, a4₂, o₂, m₂, rd₂, wr₂⟩ := addIc_ok s₁ .a4 .a4 (512 * (g - 1)) (by omega)
  refine ⟨s₂, ?_, ?_, fun r h => by rw [o₂ r h, o₁ r h], by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [endAddr, show ([Instr.addi .a4 sb ((8 * keySlot + 512 : Nat) : Int),
        .addi .a4 .a4 ((512 * (g - 1) : Nat) : Int)] : List Instr) =
      [.addi .a4 sb ((8 * keySlot + 512 : Nat) : Int)] ++ [.addi .a4 .a4 ((512 * (g - 1) : Nat) : Int)] from rfl,
      runBlock_append', e₁, Option.bind_some, e₂]
  · rw [a4₂, a4₁, addr_add, show 8 * keySlot + 512 + 512 * (g - 1) = 8 * keySlot + 512 * g by omega]

/-- The block at `p`, through a frame apart from it. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : Spec.Camellia.blockAt m' p = Spec.Camellia.blockAt m p := by
  refine Vector.ext fun i hi => ?_
  simp only [Spec.Camellia.blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 16⟩) hd (by show (16 : Nat) ≤ 2 ^ 64; decide) hi

/-- The eight blocks of the tail buffer, with ECB's scratch buffer in the
frame at `B` writable and holding the table of the words `w`. -/
theorem cryptBody_wp (d : Dir) {R : Nat} (hR : R = 18 ∨ R = 24) {s : State} {B : Addr} {w : List (BitVec 64)}
    (hB : s.gpr Impl.Modes.RISCV64.sb = B) (hal : (ecbA B).toNat % 8 = 0)
    (hw : (⟨ecbA B, 8 * slots⟩ : Region) ∈ s.wr) (hfit : (ecbA B).toNat + 8 * slots ≤ 2 ^ 64)
    (hr : ReadyAt d R s.mem (ecbA B) w) :
    WP isa (cryptBlocks R) s fun s' => s'.gpr Impl.Modes.RISCV64.sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      ReadyAt d R s'.mem (ecbA B) w ∧ Frame [⟨ecbA B, 8 * slots⟩] s.mem s'.mem ∧
      Spec.Camellia.blockAt s'.mem (ecbA B + BitVec.ofNat 64 (8 * tailSlot)) =
        blockFn (Spec.Camellia.subkeysOfWords R w) (specDir d)
          (Spec.Camellia.blockAt s.mem (ecbA B + BitVec.ofNat 64 (8 * tailSlot))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  generalize hb : ecbA B = b at hal hw hfit hr
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  have hg : g = 3 ∨ g = 4 := by omega
  obtain ⟨s₁, e₁, t0₁, a2₁, a3₁, ra₁, o₁, m₁, rd₁, wr₁, -⟩ := park_ok hB (hb ▸ hal) (hb ▸ hw)
  obtain ⟨s₂, e₂, sb₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ sb t0
  have b₂ : s₂.gpr sb = b := sb₂.trans (t0₁.trans hb)
  obtain ⟨s₃, e₃, sv₃, g₃, rd₃, wr₃, f₃, sl₃⟩ := save_ok (by rw [wr₂, wr₁]; exact hw) b₂ hal
  obtain ⟨s₄, e₄, a4₄, o₄, m₄, rd₄, wr₄⟩ := endAddr_ok s₃ (g := g) (by omega)
  unfold cryptBlocks
  rw [hgR]
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [runBlock_append', runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃,
      Option.bind_some, e₄], ?_⟩)
  have b₄ : s₄.gpr sb = b := by rw [o₄ _ (by decide), g₃, b₂]
  have hw₄ : (⟨b, 8 * slots⟩ : Region) ∈ s₄.wr := by rw [wr₄, wr₃, wr₂, wr₁]; exact hw
  -- The masks and the table, as on entry.
  have F₁ : Frame [⟨raA B, 16⟩] s.mem s₂.mem := by rw [m₂, m₁]; exact park_frame _ _ _ _
  have pres : ∀ k, (48 ≤ k ∧ k < 59) ∨ (keySlot ≤ k ∧ k < slots) →
      s₄.mem.readW (wordAddr b k) 64 = s.mem.readW (wordAddr b k) 64 := by
    intro k hk
    have hk' : (k < savedSlot ∨ savedSlot + 12 ≤ k) ∧ k < 400 := by
      rw [savedSlot_eq]; rw [keySlot_eq, slots_eq] at hk; omega
    have := sl₃ k hk'.1 (Nat.lt_trans hk'.2 (by decide))
    change s₃.mem.readW (wordAddr (s₃.gpr sb) k) 64 = s₂.mem.readW (wordAddr (s₂.gpr sb) k) 64 at this
    rw [g₃, b₂] at this
    rw [m₄, this]
    refine F₁.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [raA, hb]
    rw [keySlot_eq, slots_eq] at hk
    rcases hk with hk | hk
    · exact VG.Offset.disjoint b (.inl (by rw [raSlot_eq]; omega)) (by omega) (by rw [raSlot_eq]; decide)
    · exact VG.Offset.disjoint b (.inr (by rw [raSlot_eq]; omega)) (by omega) (by rw [raSlot_eq]; decide)
  let E : Nat → BitVec 64 := fun i => w.getD (permOf d g i) 0
  have hcore : CorePre s₄ g E :=
    { scr := by rw [b₄]; exact hw₄
      al := by rw [b₄]; exact hal
      fit := by rw [b₄]; exact hfit
      nk34 := by omega
      masks := fun kv hkv => by
        show s₄.mem.readW (wordAddr (s₄.gpr sb) kv.1) 64 = kv.2
        rw [b₄, pres _ (.inl (allMasks_range kv hkv))]
        exact hr.1 kv hkv
      keys := fun i hi => by
        have := hr.2 i (by rw [hgR]; exact hi)
        rw [hgR] at this
        refine this.congr fun j hj => ?_
        rw [b₄, entryW_word, entryW_word, pres _ (.inr ⟨by omega, by rw [keySlot_eq, slots_eq]; omega⟩)]
      hg := hg
      bound := by rw [a4₄, o₄ _ (by decide), g₃] }
  refine WP.seq (WP.mono (crypt8_ok hcore) fun s₅ ⟨c₅, k₅⟩ => ?_)
  have b₅ : s₅.gpr sb = b := by rw [c₅.base, b₄]
  have f₅ : Frame (ctxRegions b) s₄.mem s₅.mem := by have := c₅.frame; rwa [b₄] at this
  have sv₅ : Saved s₂ b s₅.mem := fun i hi => by
    rw [← sv₃ i hi, ← m₄]
    refine f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (d := 8 * (savedSlot + i)) (by omega) (by rw [savedSlot_eq]; omega)
    · exact VG.Offset.disjoint b (.inl (by rw [savedSlot_eq, tailSlot_eq]; omega)) (by rw [savedSlot_eq]; omega)
        (by rw [tailSlot_eq]; decide)
  obtain ⟨s₆, e₆, rg₆, ro₆, m₆, rd₆, wr₆⟩ := restore_ok (by rw [c₅.wr]; exact hw₄) b₅ hal sv₅
  have b₆ : s₆.gpr sb = ecbA B := (ro₆ sb a5_ne_sreg).trans (b₅.trans hb.symm)
  obtain ⟨s₇, e₇, s1₇, s2₇, s3₇, s4₇, ra₇, a0₇, o₇, m₇, rd₇, wr₇, -⟩ :=
    unpark_ok b₆ (hb ▸ hal) (by rw [wr₆, c₅.wr, hb]; exact hw₄)
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_append', e₆, Option.bind_some, e₇], ?_⟩
  have mem₇ : s₇.mem = s₅.mem := by rw [m₇, m₆]
  -- `park`'s slots.
  have slot : ∀ k, savedSlot + 12 ≤ k → k < savedSlot + 14 →
      s₅.mem.readW (b + BitVec.ofNat 64 (8 * k)) 64 = s₂.mem.readW (b + BitVec.ofNat 64 (8 * k)) 64 := by
    intro k h1 h2
    rw [savedSlot_eq] at h1 h2
    rw [f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), m₄,
      f₃.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · simp only [savedRegion, List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint b (.inr (by rw [savedSlot_eq]; omega)) (by omega) (by rw [savedSlot_eq]; decide)
    · simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Offset.disjoint_base b (by rw [savedSlot_eq]; omega) (by omega)
      · exact VG.Offset.disjoint b (.inl (by rw [tailSlot_eq]; omega)) (by omega) (by rw [tailSlot_eq]; decide)
  have pr := park_read s.mem B (s.gpr .ra) (s.gpr .a0)
  rw [← m₁, ← m₂] at pr
  have hra : s₅.mem.readW (raA B) 64 = s.gpr .ra := by
    rw [raA, hb, slot raSlot (by decide) (by decide), ← hb]; exact pr.1
  have ha0 : s₅.mem.readW (a0A B) 64 = s.gpr .a0 := by
    rw [a0A, hb, slot a0Slot (by decide) (by decide), ← hb]; exact pr.2
  have r₅ : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → r ≠ .a4 → r ≠ sb → s₅.gpr r = s₁.gpr r :=
    fun r a b' c e f => by rw [c₅.keep r a b' c, o₄ r e, g₃, o₂ r f]
  -- The tail buffer, on entry to the rounds.
  have tail₄ : Spec.Camellia.blockAt s₄.mem (b + BitVec.ofNat 64 (8 * tailSlot)) =
      Spec.Camellia.blockAt s.mem (b + BitVec.ofNat 64 (8 * tailSlot)) := by
    rw [m₄, blockAt_frame f₃ fun r hr => ?_, blockAt_frame F₁ fun r hr => ?_]
    · simp only [List.mem_singleton] at hr; subst hr
      rw [raA, hb]
      exact VG.Offset.disjoint b (.inr (by rw [raSlot_eq, tailSlot_eq]; decide)) (by rw [tailSlot_eq]; decide)
        (by rw [raSlot_eq]; decide)
    · simp only [savedRegion, List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint b (.inr (by rw [savedSlot_eq, tailSlot_eq]; decide)) (by rw [tailSlot_eq]; decide)
        (by rw [savedSlot_eq]; decide)
  refine ⟨s4₇, kept_of hB (s₄ := s₅) (s₀ := s₂)
      (by rw [r₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a2₁)
      (by rw [r₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a3₁)
      (by rw [r₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ra₁)
      (fun r hr h1 h2 h3 h4 => by
        have : r ≠ sb ∧ r ≠ .t0 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .ra := by
          simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [o₂ r this.1, o₁ r this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2])
      (by rw [s1₇, ro₆ _ a2_ne_sreg]) (by rw [s2₇, ro₆ _ a3_ne_sreg]) (by rw [s3₇, ro₆ _ ra_ne_sreg]) s4₇
      (by rw [ra₇, m₆]; exact hra) (by rw [a0₇, m₆]; exact ha0)
      (fun i hi h1 h2 h3 h4 => by
        rw [o₇ _ h1 h2 h3 h4 (fun h => ra_ne_sreg i hi h.symm) (fun h => a0_ne_sreg i hi h.symm), rg₆ i hi]),
    ⟨?_, fun i hi => ?_⟩, ?_, ?_, by rw [rd₇, rd₆, c₅.rd, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₇, wr₆, c₅.wr, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [mem₇]; exact c₅.masks.at b₅
  · rw [mem₇]
    have := hr.2 i hi
    rw [hgR] at hi this ⊢
    refine this.congr fun j hj => ?_
    have hj' : keySlot ≤ keySlot + 8 * i + j ∧ keySlot + 8 * i + j < slots := ⟨by omega, by
      rw [keySlot_eq, slots_eq]; omega⟩
    rw [entryW_word, entryW_word, f₅.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide),
      pres _ (.inr hj')]
    simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [keySlot_eq] at hj'
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by simp only [keySlot_eq, savedSlot_eq]; omega)
        (by simp only [keySlot_eq, slots_eq] at hj' ⊢; omega)
    · exact VG.Offset.disjoint b (.inr (by simp only [keySlot_eq, tailSlot_eq]; omega))
        (by simp only [keySlot_eq, slots_eq] at hj' ⊢; omega) (by rw [tailSlot_eq]; decide)
  · rw [mem₇]
    have F₃ : Frame [⟨b, 8 * slots⟩] s₂.mem s₄.mem := by
      rw [m₄]; refine f₃.sub fun r hr => ?_
      simp only [savedRegion, List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, VG.Offset.sub_base b (by decide)⟩
    have F₅ : Frame [⟨b, 8 * slots⟩] s₄.mem s₅.mem := f₅.sub fun r hr => by
      simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, VG.Offset.sub_base b (by decide)⟩
    have F₁' : Frame [⟨b, 8 * slots⟩] s.mem s₂.mem := F₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by rw [raA, hb]; exact VG.Offset.sub_base b (by rw [slots_eq]; decide)⟩
    exact (F₁'.trans F₃).trans F₅
  · have := k₅ 0 (by decide)
    simp only [blk, b₅, b₄, Nat.mul_zero, Nat.add_zero] at this
    rw [mem₇, this, tail₄]
    simp only [E]
    rw [← hgR, crypt_spec d hR]

/-! ## The core -/

theorem total_eq (d : Dir) (R : Nat) : (dirCore d R).total = 406 := rfl

theorem layout (d : Dir) (R : Nat) : Layout (dirCore d R) :=
  ⟨by dsimp only [dirCore]; decide, .inr rfl, by dsimp only [dirCore]; decide, by dsimp only [dirCore]; decide,
    by dsimp only [dirCore]; decide, by dsimp only [dirCore]; decide, by dsimp only [dirCore]; decide⟩

/-- ECB's scratch buffer within the frame. -/
theorem ecb_in {s : State} {B : Addr} {d : Dir} {R : Nat} (hS : ScrIn s B (dirCore d R).total) :
    InRegions s.wr (ecbA B) (8 * slots) :=
  ⟨_, hS.whole (by rw [total_eq]; decide), VG.Offset.contains_base B (by rw [total_eq]; decide) (by decide)⟩

theorem ecb_sub (d : Dir) (R : Nat) (B : Addr) :
    Region.Sub ⟨ecbA B, 8 * slots⟩ ⟨B, 8 * (dirCore d R).total⟩ :=
  VG.Offset.sub_base B (by rw [total_eq]; decide)

theorem ecb_al {s : State} {B : Addr} {d : Dir} {R : Nat} (hS : ScrIn s B (dirCore d R).total) :
    (ecbA B).toNat % 8 = 0 :=
  Spill.al8 (by have := hS.al; omega) (by decide)

theorem ecb_fit {s : State} {B : Addr} {d : Dir} {R : Nat} (hS : ScrIn s B (dirCore d R).total) :
    (ecbA B).toNat + 8 * slots ≤ 2 ^ 64 := by
  have h := hS.fit
  have e : (dirCore d R).total = 406 := rfl
  rw [e] at h
  rw [slots_eq, ecbA, ecbOff_eq, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 48 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem prepare_noFrames (d : Dir) (R : Nat) : (dirCore d R).prepare.noFrames = true := by
  cases d <;> rfl

theorem crypt_noFrames (d : Dir) (R : Nat) : (dirCore d R).crypt.noFrames = true := rfl

theorem prepare_wp (d : Dir) {R : Nat} (hR : R = 18 ∨ R = 24) {s : State} {B : Addr} {rs : List Region}
    {w : List (BitVec 64)} (hB : s.gpr Impl.Modes.RISCV64.sb = B) (hS : ScrIn s B (dirCore d R).total)
    (hm : (⟨B, 8 * (dirCore d R).total⟩ : Region) ∈ rs) (hk : KeyArgs R s rs w) :
    WP isa (dirCore d R).prepare s fun s' => Ready d R s' B rs w ∧ s'.gpr Impl.Modes.RISCV64.sb = B ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ Frame [coreRegion (dirCore d R) B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, hws, hin, hfit, hdis⟩ := hk
  have dSS : Region.Disjoint ⟨p, 272⟩ ⟨ecbA B, 8 * slots⟩ := (hdis _ hm).sub_right (ecb_sub d R B)
  have w₀ := prepBody_wp d hR (s := s.withRegions [⟨p, 272⟩] [⟨ecbA B, 8 * slots⟩]) hB (ecb_al hS)
    (List.mem_singleton_self _) (ecb_fit hS) hp (List.mem_singleton_self _) hfit dSS
  refine WP.narrow w₀ (VG.Covers.append (VG.Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hin) (VG.Covers.one (ecb_in hS)))
    (VG.Covers.one (ecb_in hS)) (fun s' rd' wr' _ f' ⟨b', k', r', _, _, _⟩ => ?_) (prepare_noFrames d R)
  refine ⟨?_, b', fun r hr => k' r hr, f', rd', wr'⟩
  rw [hws]; exact r'

/-- Block `j` of blocks transformed by ECB. -/
theorem crypt_wp (d : Dir) {R : Nat} (hR : R = 18 ∨ R = 24) {s : State} {B : Addr} {ws : List Region}
    {w : List (BitVec 64)} (hB : s.gpr Impl.Modes.RISCV64.sb = B) (hS : ScrIn s B (dirCore d R).total)
    (hr : Ready d R s B ws w) :
    WP isa (dirCore d R).crypt s fun s' => s'.gpr Impl.Modes.RISCV64.sb = B ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Ready d R s' B ws w ∧ Frame [coreRegion (dirCore d R) B] s.mem s'.mem ∧
      (∀ j < (dirCore d R).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d R) B j) (4 * (dirCore d R).bw) =
        dirCipher d (Spec.Camellia.subkeysOfWords R w)
          (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d R) B j) (4 * (dirCore d R).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w₀ := cryptBody_wp d hR (s := s.withRegions [] [⟨ecbA B, 8 * slots⟩]) hB (ecb_al hS)
    (List.mem_singleton_self _) (ecb_fit hS) hr
  refine WP.narrow w₀ (VG.Covers.append VG.Covers.nil (VG.Covers.one (ecb_in hS))) (VG.Covers.one (ecb_in hS))
    (fun s' rd' wr' _ f' ⟨b', k', r', _, blk', _, _⟩ => ⟨b', fun r hr => k' r hr, r', f', fun j hj => ?_, rd', wr'⟩)
    (crypt_noFrames d R)
  obtain rfl : j = 0 := by have : (dirCore d R).G = 1 := rfl; omega
  have ha : blkAddr (dirCore d R) B 0 = ecbA B + BitVec.ofNat 64 (8 * tailSlot) := by
    show B + BitVec.ofNat 64 (8 * 102) + BitVec.ofNat 64 (16 * 0) = B + BitVec.ofNat 64 48 + BitVec.ofNat 64 768
    rw [VG.Offset.add_add, VG.Offset.add_add]
  show Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d R) B 0) 16 =
    dirCipher d _ (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d R) B 0) 16)
  rw [dirCipher_bytes, bytesAt_eq_blockAt, ha]
  exact congrArg Vector.toList blk'

/-- Camellia's core meets what the modes need. -/
def dirCoreSpec (d : Dir) (R : Nat) (hR : R = 18 ∨ R = 24) : CoreSpec (dirCore d R) where
  Key := List (BitVec 64)
  cipher k := dirCipher d (Spec.Camellia.subkeysOfWords R k)
  KeyArgs := KeyArgs R
  Ready := Ready d R
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Camellia.cipher, Spec.Camellia.invCipher, dirCore]
  layout := layout d R
  keyArgs_congr h e r _ _ f := keyArgs_congr h e.a0 r f hR
  ready_frame h _ _ _ _ f _ hd := ready_frame hR h f hd
  prepare_wp := prepare_wp d hR
  crypt_wp := crypt_wp d hR

end VG.Proof.Camellia.RISCV64.Mode
