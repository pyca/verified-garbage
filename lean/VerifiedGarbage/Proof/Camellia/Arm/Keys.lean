module
public import VerifiedGarbage.Proof.Camellia.Arm.Core

import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.Arm.Fl
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The table of bitsliced subkeys on ARMv7

`encKeys g` and `decKeys g` bitslice the subkeys of the schedule at `r12`
into the table at slot 72, entry `i` holding the subkey word `perm i`:
`keyOne_step` is one subkey, each of its two 32-bit words loaded and turned
into its eight planes (`keyPlanes`, checked by evaluation), and
`keyLoop_wp` the loop of them, counted down in `lr`.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Bitslice (lanes)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp ldS stS)
open VG.Proof.Sm4.Arm (linPostG linG_ok)
open VG.Proof.Camellia (byteOf_wordAt)

/-- The table's entry `e` holds `k` for every block. -/
abbrev EntryOk (m : Mem) (b : BitVec 32) (e : Nat) (k : BitVec 64) : Prop :=
  W32.HalfRel (entryW m b e) fun _ => k

/-- The scratch buffer at `b` and the schedule's 34 words at `sched`, apart. -/
structure KeyPre (s : State) (b sched : BitVec 32) : Prop where
  base : s.gpr sb = b
  scr : Scr s b
  sch : (⟨State.addr sched, 272⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 272 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr sched, 272⟩ ⟨State.addr b, 4 * slots⟩

theorem KeyPre.congr {s s' : State} {b sched : BitVec 32} (h : KeyPre s b sched) (hb : s'.gpr sb = s.gpr sb)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : KeyPre s' b sched :=
  ⟨hb.trans h.base, ⟨hwr ▸ h.scr.wr, h.scr.fit⟩, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

/-- Word `v` of subkey `w` of the schedule. -/
theorem KeyPre.addr {sched : BitVec 32} (hfit : sched.toNat + 272 ≤ 2 ^ 32) {w v : Nat} (hw : 8 * w + v < 272) :
    State.addr (sched + BitVec.ofNat 32 (8 * w) + BitVec.ofNat 32 v) =
      State.addr sched + BitVec.ofNat 64 (8 * w + v) := by
  rw [add_ofNat_ofNat, VG.Arm.addr_add (by omega_arith)]

theorem KeyPre.word_in {s : State} {b sched : BitVec 32} (h : KeyPre s b sched) {w v : Nat}
    (hw : 8 * w + v + 4 ≤ 272) :
    InRegions (s.rd ++ s.wr) (State.addr (sched + BitVec.ofNat 32 (8 * w) + BitVec.ofNat 32 v)) 4 := by
  refine ⟨_, h.sch, ?_⟩
  rw [KeyPre.addr h.schFit (by omega_arith)]
  exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- The schedule is outside the scratch buffer. -/
theorem KeyPre.wordAt_eq {s : State} {b sched : BitVec 32} (h : KeyPre s b sched) {m m' : Mem}
    (hf : Frame [⟨State.addr b, 4 * slots⟩] m m') {w : Nat} (hw : w < 34) :
    Spec.Camellia.wordAt m' (State.addr sched + BitVec.ofNat 64 (8 * w)) =
      Spec.Camellia.wordAt m (State.addr sched + BitVec.ofNat 64 (8 * w)) := by
  refine VG.Proof.Camellia.wordAt_frame hf fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact h.sep.sub_left (VG.Offset.sub_base _ (by omega_arith))

/-- The entry at `kp`, for the planes' stores. -/
theorem ok_entry {s : State} {b : BitVec 32} {e : Nat} (hs : Scr s b) (hk : AtEntry s b e) (he : e < 34) :
    Ok entryCfg s where
  slotIn k hk' := by
    simp only [entryCfg] at hk' ⊢
    rw [wordAddr_entry hk]; exact hs.slot_in (by rw [slots_eq, keySlot_eq]; omega_arith)
  extIn k hk' := by simp [entryCfg] at hk'
  slots := by
    have := hs.fit
    simp only [entryCfg]
    rw [hk, BitVec.toNat_add, BitVec.toNat_ofNat, keySlot_eq]
    rw [slots_eq] at this
    rw [Nat.mod_eq_of_lt (a := 4 * 72 + 64 * e) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  sep k _ j hj := by simp [entryCfg] at hj

theorem keyPlanes_all (w : Nat) (hw : w = 0 ∨ w = 1) :
    (layerKeep.all fun r => (keyPlanes w).all fun i => !clobbers i r) = true ∧
    ((keyPlanes w).all fun i => !clobbers i u7) = true ∧
    ((keyPlanes w).all fun i => !clobbers i .lr) = true ∧
    ((keyPlanes w).all fun i => !clobbers i (q 4)) = true := by
  rcases hw with rfl | rfl <;> decide +kernel

/-- The registers the table's construction writes. -/
def keyWrites : List Reg := [q 4, q 5, t1, u7, .lr]

theorem keyPlanes_dst (w : Nat) (hw : w = 0 ∨ w = 1) :
    ((keyPlanes w).all fun i => (dsts i).all fun r => r == q 5 || r == t1) = true := by
  rcases hw with rfl | rfl <;> decide +kernel

theorem keyPlanes_keep (w : Nat) (hw : w = 0 ∨ w = 1) (r : Reg) (hr : r ∉ keyWrites) :
    ((keyPlanes w).all fun i => !clobbers i r) = true := by
  have h5 : r ≠ q 5 := fun h => hr (by rw [h]; decide)
  have h11 : r ≠ t1 := fun h => hr (by rw [h]; decide)
  refine List.all_eq_true.mpr fun i hi => ?_
  rw [clobbers_eq_false_of_all (List.all_eq_true.mp (keyPlanes_dst w hw) i hi)
    (by simp [h5, h11])]
  rfl

/-- The planes of the word in `q 4` to words `8 w …` of the entry `e` at `kp`. -/
theorem keyPlanes_step {s : State} {b : BitVec 32} {e w : Nat} (hs : Scr s b)
    (hk : AtEntry s b e) (he : e < 34) (hw : w = 0 ∨ w = 1) :
    ∃ s', runBlock isa (keyPlanes w) s = some s' ∧
      (∀ j < 8, ∀ p < 32, (entryW s'.mem b e (8 * w + j)).getLsbD p = (s.gpr (q 4)).getLsbD (8 * (p / 8) + j)) ∧
      (∀ j < 16, j < 8 * w ∨ 8 * w + 8 ≤ j → entryW s'.mem b e j = entryW s.mem b e j) ∧
      (∀ r, r ∉ keyWrites → s'.gpr r = s.gpr r) ∧ s'.gpr u7 = s.gpr u7 ∧ s'.gpr .lr = s.gpr .lr ∧
      s'.gpr (q 4) = s.gpr (q 4) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨State.addr (b + BitVec.ofNat 32 (4 * (keySlot + 16 * e))), 64⟩] s.mem s'.mem := by
  have hchk : check (lanes 32 10) entryCfg (linExt 0) (keyPlanes w) keyEnv
      (linPostG 10 [] (keyOuts w) (keyKeep w) keyEnv) = true := by
    rcases hw with rfl | rfl
    · exact keyPlanes0_check
    · exact keyPlanes1_check
  let W : Nat → BitVec 32 := fun i => if i = 0 then s.gpr (q 4) else s.mem.readW (wordAddr (s.gpr kp) (i - 1)) 32
  obtain ⟨s', h', -, so', ko', rd', wr', -, o', f', -, -⟩ := linG_ok hchk (ok_entry hs hk he) W
    (fun r i hri => by simp at hri; obtain ⟨rfl, rfl⟩ := hri; exact ⟨by decide, rfl⟩)
    (fun j i hji => by
      simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk', rfl, rfl⟩ := hji
      exact ⟨by simp only [entryCfg]; omega_arith, by omega_arith, by simp [W]; rfl⟩)
    (fun kv hkv => by simp at hkv) (fun j hj => by simp [entryCfg] at hj)
  obtain ⟨-, a2, a3, a4⟩ := keyPlanes_all w hw
  have hkeep : ∀ r, r ∉ keyWrites → s'.gpr r = s.gpr r := fun r hr => o' r (keyPlanes_keep w hw r hr)
  have hkp : s'.gpr kp = s.gpr kp := hkeep _ (by decide)
  refine ⟨s', h', fun j hj p hp => ?_, fun j hj hjw => ?_, hkeep, o' _ a2, o' _ a3, o' _ a4, rd', wr', ?_⟩
  · have := so' (8 * w + j) (keyBsG j)
      (by simp only [keyOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      (by simp only [entryCfg]; rcases hw with rfl | rfl <;> omega_arith) p hp
    simp only [entryCfg] at this
    rw [entryW, ← wordAddr_entry hk, this, keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false]
    simp only [bitOf]
    rw [Nat.div_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    rfl
  · have := ko' j (by
      simp only [keyKeep, List.mem_map, List.mem_range]
      rcases hw with rfl | rfl
      · exact ⟨j - 8, by omega_arith, by omega_arith⟩
      · exact ⟨j, by omega_arith, by omega_arith⟩) (by simp only [entryCfg]; omega_arith)
    simp only [entryCfg] at this
    rw [entryW, entryW, ← wordAddr_entry hk, this]
  · refine f'.mono fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, entryCfg, List.mem_singleton]
    rw [hk, keySlot_eq, show 4 * 72 + 64 * e = 4 * (72 + 16 * e) by omega_arith]

/-- The entry `e` of the table. -/
def entryRegion (b : BitVec 32) (e : Nat) : Region := ⟨State.addr (b + BitVec.ofNat 32 (4 * (keySlot + 16 * e))), 64⟩

theorem encodable_64 : encodable (BitVec.ofNat 32 64) = true := by decide

theorem keyOne_eq (d : Nat) : keyOne d = (.ldr (q 4) .r12 d :: keyPlanes 0) ++
    ((.ldr (q 4) .r12 (d + 4) :: keyPlanes 1) ++ ([.dp .add kp kp (.imm (BitVec.ofNat 32 64))] : List Instr)) := by
  rfl

/-- The entry's region is disjoint from the schedule's. -/
theorem KeyPre.entry_sep {s : State} {b sched : BitVec 32} (h : KeyPre s b sched) {e : Nat} (he : e < 34) :
    Region.Disjoint ⟨State.addr sched, 272⟩ (entryRegion b e) := by
  have hf := h.scr.fit
  rw [slots_eq] at hf
  refine h.sep.sub_right ?_
  simp only [entryRegion]
  rw [VG.Arm.addr_add (by rw [keySlot_eq]; omega_arith)]
  exact VG.Offset.sub_base _ (by rw [slots_eq, keySlot_eq]; omega_arith)

/-- One subkey: the two words of schedule word `w + d / 8`, at `[r12 + d]`,
to entry `e`. -/
theorem keyOne_step {s : State} {b sched : BitVec 32} {d e w : Nat} (hd : d = 0 ∨ d = 8)
    (hk : KeyPre s b sched) (hr : s.gpr u7 = sched + BitVec.ofNat 32 (8 * w)) (hw : w + d / 8 < 34)
    (hkp : AtEntry s b e) (he : e < 34) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧ AtEntry s' b (e + 1) ∧
      (∀ r, r ∉ keyWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.gpr u7 = s.gpr u7 ∧
      s'.gpr .lr = s.gpr .lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [entryRegion b e] s.mem s'.mem ∧
      EntryOk s'.mem b e (Spec.Camellia.wordAt s.mem (State.addr sched + BitVec.ofNat 64 (8 * (w + d / 8)))) := by
  have hs := hk.scr
  have hr' : s.gpr .r12 = sched + BitVec.ofNat 32 (8 * w) := hr
  -- The first word.
  have hin₀ : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 d)) 4 := by
    rw [hr']; exact hk.word_in (by omega_arith)
  let s₁ := s.setReg (q 4) (s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 d)) 32)
  have e₁ : exec (.ldr (q 4) .r12 d) s = some s₁ := exec_ldr (by omega_arith) hin₀
  have k₁ := keeps_setReg s (s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 d)) 32)
    (d := q 4) (by decide) (by decide)
  have hs₁ : Scr s₁ b := ⟨by rw [k₁.wr]; exact hs.wr, hs.fit⟩
  obtain ⟨s₂, e₂, p₂, o₂, g₂, u₂, l₂, q₂, rd₂, wr₂, f₂⟩ := keyPlanes_step (w := 0) (e := e) hs₁
    (by rw [AtEntry, k₁.gpr _ (by decide)]; exact hkp) he (.inl rfl)
  -- The second word.
  have hr₂ : s₂.gpr .r12 = s.gpr .r12 := by rw [show (Reg.r12) = u7 from rfl, u₂, k₁.gpr _ (by decide)]
  have hin₄ : InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (d + 4))) 4 := by
    rw [hr₂, hr', rd₂, wr₂, k₁.rd, k₁.wr]; exact hk.word_in (by omega_arith)
  have hm₂ : s₂.mem.readW (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (d + 4))) 32 =
      s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 (d + 4))) 32 := by
    rw [hr₂, ← k₁.mem]
    refine f₂.readW (r := ⟨State.addr sched, 272⟩) ?_ (fun r hr' => ?_) (by decide)
    · rw [hr', KeyPre.addr hk.schFit (by omega_arith)]
      exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr'; subst hr'
      exact hk.entry_sep he
  let s₃ := s₂.setReg (q 4) (s₂.mem.readW (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (d + 4))) 32)
  have e₃ : exec (.ldr (q 4) .r12 (d + 4)) s₂ = some s₃ := exec_ldr (by omega_arith) hin₄
  have k₃ := keeps_setReg s₂ (s₂.mem.readW (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (d + 4))) 32)
    (d := q 4) (by decide) (by decide)
  have hs₃ : Scr s₃ b := ⟨by rw [k₃.wr, wr₂, k₁.wr]; exact hs.wr, hs.fit⟩
  have hkp₃ : AtEntry s₃ b e := by
    rw [AtEntry, k₃.gpr _ (by decide), g₂ _ (by decide), k₁.gpr _ (by decide)]; exact hkp
  obtain ⟨s₄, e₄, p₄, o₄, g₄, u₄, l₄, q₄, rd₄, wr₄, f₄⟩ := keyPlanes_step (w := 1) (e := e) hs₃ hkp₃ he (.inr rfl)
  -- `kp += 64`.
  have hkp₄ : s₄.gpr kp = s.gpr kp := by
    rw [g₄ _ (by decide), k₃.gpr _ (by decide), g₂ _ (by decide), k₁.gpr _ (by decide)]
  have hrd : s₄.rd = s.rd := by rw [rd₄, k₃.rd, rd₂, k₁.rd]
  have hwr : s₄.wr = s.wr := by rw [wr₄, k₃.wr, wr₂, k₁.wr]
  have hw4 : 8 * w + d + 8 ≤ 272 := by omega_arith
  have hent : ∀ v < 2, ∀ j < 8, ∀ p < 32, (entryW s₄.mem b e (8 * v + j)).getLsbD p =
      (s.mem (State.addr sched + BitVec.ofNat 64 (8 * (w + d / 8) + (4 * v + p / 8)))).getLsbD j := by
    intro v hv j hj p hp
    rcases (show v = 0 ∨ v = 1 by omega_arith) with rfl | rfl
    · rw [Nat.mul_zero, Nat.zero_add, o₄ j (by omega_arith) (.inl (by omega_arith)),
        show entryW s₃.mem b e j = entryW s₂.mem b e j by rw [k₃.mem]]
      have := p₂ j hj p hp
      rw [Nat.mul_zero, Nat.zero_add] at this
      rw [this]
      show (s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 d)) 32).getLsbD _ = _
      rw [W32.readW32_bit _ _ (by omega_arith) hj, hr', KeyPre.addr hk.schFit (by omega_arith), VG.Offset.add_add,
        show 8 * w + d + p / 8 = 8 * (w + d / 8) + (4 * 0 + p / 8) by omega_arith]
    · rw [p₄ j hj p hp]
      show (s₂.mem.readW (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (d + 4))) 32).getLsbD _ = _
      rw [hm₂, W32.readW32_bit _ _ (by omega_arith) hj, hr', KeyPre.addr hk.schFit (by omega_arith), VG.Offset.add_add,
        show 8 * w + (d + 4) + p / 8 = 8 * (w + d / 8) + (4 * 1 + p / 8) by omega_arith]
  let s₅ := s₄.setReg kp (s₄.gpr kp + BitVec.ofNat 32 64)
  refine ⟨s₅, ?_, hkp.add (n := 1) (by rw [RegUpd.gpr_setReg_self, hkp₄]), fun r h1 h2 => ?_, ?_, ?_,
    by rw [RegUpd.rd_setReg, hrd], by rw [RegUpd.wr_setReg, hwr], ?_, ?_⟩
  · rw [keyOne_eq, runBlock_app, runBlock_cons, e₁, runStep_some, e₂, Option.bind_some, runBlock_app,
      runBlock_cons, e₃, runStep_some, e₄, Option.bind_some, addKp_ok _ _ encodable_64]
  · rw [RegUpd.gpr_setReg_of_ne _ _ h2, g₄ r h1, k₃.gpr _ (fun h => h1 (by rw [h]; decide)), g₂ r h1,
      k₁.gpr _ (fun h => h1 (by rw [h]; decide))]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), u₄, k₃.gpr _ (by decide), u₂, k₁.gpr _ (by decide)]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), l₄, k₃.gpr _ (by decide), l₂, k₁.gpr _ (by decide)]
  · rw [RegUpd.mem_setReg]
    refine (by rw [← k₁.mem]; exact f₂ : Frame [entryRegion b e] s.mem s₂.mem).trans ?_
    rw [← k₃.mem]; exact f₄
  · intro b' hb c hc j hj
    show (entryW s₄.mem b e _).getLsbD _ = _
    rw [show 8 * (c / 4) + j = 8 * (c / 4) + j from rfl, hent (c / 4) (by omega_arith) j hj _ (by omega_arith),
      byteOf_wordAt _ _ hc, VG.Offset.add_add,
      show 8 * (w + d / 8) + (4 * (c / 4) + (8 * (c % 4) + b') / 8) = 8 * (w + d / 8) + c by omega_arith]

/-! ## The loops -/

/-- The table's entries. -/
def tableRegion (b : BitVec 32) : Region := ⟨State.addr (b + BitVec.ofNat 32 (4 * keySlot)), 4 * (16 * 34)⟩

theorem entry_sub_table {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e : Nat} (he : e < 34) :
    Region.Sub (entryRegion b e) (tableRegion b) := by
  rw [slots_eq] at hfit
  simp only [entryRegion, tableRegion]
  rw [VG.Arm.addr_add (by rw [keySlot_eq]; omega_arith), VG.Arm.addr_add (by rw [keySlot_eq]; omega_arith)]
  exact VG.Offset.sub _ (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)

theorem table_sub_scr {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    Region.Sub (tableRegion b) ⟨State.addr b, 4 * slots⟩ := by
  rw [slots_eq] at hfit
  simp only [tableRegion]
  rw [VG.Arm.addr_add (by rw [keySlot_eq]; omega_arith)]
  exact VG.Offset.sub_base _ (by rw [keySlot_eq, slots_eq]; omega_arith)

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e i : Nat}
    (hf : Frame [entryRegion b e] m m') (hi : i < 34) (he : e < 34) (hie : i ≠ e) {j : Nat} (hj : j < 16) :
    entryW m' b i j = entryW m b i j := by
  rw [slots_eq] at hfit
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  simp only [entryRegion]
  rw [wordAddr, VG.Arm.addr_add (by rw [keySlot_eq]; omega_arith), VG.Arm.addr_add (by rw [keySlot_eq]; omega_arith)]
  exact VG.Offset.disjoint _ (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)

/-- What the loops keep, after `k` of their `N` iterations: the subkeys `F`
in the entries before `e₀ + k`, `r12` at word `wk k` of the schedule. -/
structure KeyInv (s₀ : State) (b sched : BitVec 32) (e₀ N : Nat) (wk : Nat → Nat) (F : Nat → BitVec 64)
    (k : Nat) (s : State) : Prop where
  pre : KeyPre s b sched
  kpos : AtEntry s b (e₀ + k)
  r12 : s.gpr u7 = sched + BitVec.ofNat 32 (8 * wk k)
  cnt : s.gpr .lr = BitVec.ofNat 32 (N - k)
  ent : ∀ i < e₀ + k, EntryOk s.mem b i (F i)
  frame : Frame [tableRegion b] s₀.mem s.mem
  regs : ∀ r, r ∉ keyWrites → r ≠ kp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem subs_lr (s : State) :
    runBlock isa [.subs .lr .lr (.imm 1)] s =
      some ((subFlags s (s.gpr .lr) 1).setReg .lr (s.gpr .lr - 1)) := by
  simp only [runBlock_cons, exec, Op2.eval, show encodable 1 = true by decide, ↓reduceIte, Option.map_some,
    runStep_some, runBlock_nil]

/-- The loop of `keyOne 0` and `op r12, r12, #8` (`f` on `r12`), counted down in `lr`. -/
theorem keyLoop_wp {s₀ s : State} {b sched : BitVec 32} {e₀ N : Nat} {wk : Nat → Nat} {F : Nat → BitVec 64}
    {i₁ : Instr} {f : BitVec 32 → BitVec 32}
    (hop : ∀ s : State, ∃ s', runBlock isa [i₁] s = some s' ∧
      s'.gpr .r12 = f (s.gpr .r12) ∧ (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (hN : e₀ + N ≤ 34) (hN0 : N < 2 ^ 32)
    (hwk : ∀ k < N, wk k < 34)
    (hstep : ∀ k < N, f (sched + BitVec.ofNat 32 (8 * wk k)) = sched + BitVec.ofNat 32 (8 * wk (k + 1)))
    (hF : ∀ k < N, F (e₀ + k) = Spec.Camellia.wordAt s₀.mem (State.addr sched + BitVec.ofNat 64 (8 * wk k)))
    {k : Nat} (hk : k < N) (hs : KeyInv s₀ b sched e₀ N wk F k s) :
    WP isa (.loop (.block (keyOne 0 ++ ([i₁, .subs .lr .lr (.imm 1)] : List Instr))) .ne) s
      (KeyInv s₀ b sched e₀ N wk F N) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = N - k ∧ k < N ∧ KeyInv s₀ b sched e₀ N wk F k s)
    (fun n s hs => ?_) (N - k) s ⟨k, rfl, hk, hs⟩
  obtain ⟨k, rfl, hk, hi⟩ := hs
  have hfit := hi.pre.scr.fit
  have hw := hwk k hk
  obtain ⟨s₁, e₁, kp₁, o₁, u₁, l₁, rd₁, wr₁, f₁, E₁⟩ := keyOne_step (d := 0) (e := e₀ + k) (Or.inl rfl)
    hi.pre hi.r12 (by omega_arith) hi.kpos (by omega_arith)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := hop s₁
  have e₃ := subs_lr s₂
  let s₃ := (subFlags s₂ (s₂.gpr .lr) 1).setReg .lr (s₂.gpr .lr - 1)
  have o₃ : ∀ r, r ≠ .lr → s₃.gpr r = s₂.gpr r := fun r h => by
    rw [RegUpd.gpr_setReg_of_ne _ _ h, subFlags_gpr]
  refine WP.of_runBlock ⟨s₃, by
    rw [runBlock_app, e₁, Option.bind_some,
      show ([i₁, .subs .lr .lr (.imm 1)] : List Instr) = [i₁] ++ [.subs .lr .lr (.imm 1)] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃], ?_⟩
  have ht₂ : s₂.gpr .lr = BitVec.ofNat 32 (N - k) := by rw [o₂ _ (by decide), l₁, hi.cnt]
  have hc₃ : s₃.gpr .lr = BitVec.ofNat 32 (N - (k + 1)) := by
    rw [RegUpd.gpr_setReg_self, ht₂, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show N - k - 1 = N - (k + 1) by omega_arith]
  have hm₃ : s₃.mem = s₁.mem := by rw [RegUpd.mem_setReg, subFlags_mem, m₂]
  have hinv : KeyInv s₀ b sched e₀ N wk F (k + 1) s₃ := by
    refine ⟨hi.pre.congr ?_ ?_ ?_, ?_, ?_, hc₃, fun i hi' => ?_, ?_, fun r h1 h2 => ?_,
      by rw [RegUpd.rd_setReg, subFlags_rd, rd₂, rd₁, hi.rd], by rw [RegUpd.wr_setReg, subFlags_wr, wr₂, wr₁, hi.wr]⟩
    · rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide) (by decide)]
    · rw [RegUpd.rd_setReg, subFlags_rd, rd₂, rd₁]
    · rw [RegUpd.wr_setReg, subFlags_wr, wr₂, wr₁]
    · have : AtEntry s₃ b (e₀ + k + 1) := by rw [AtEntry, o₃ _ (by decide), o₂ _ (by decide)]; exact kp₁
      simpa only [Nat.add_assoc] using this
    · rw [o₃ _ (by decide), show u7 = Reg.r12 from rfl, r₂, show Reg.r12 = u7 from rfl, u₁, hi.r12, hstep k hk]
    · by_cases he : i = e₀ + k
      · subst he
        have hw' : Spec.Camellia.wordAt s.mem (State.addr sched + BitVec.ofNat 64 (8 * (wk k + 0 / 8))) =
            F (e₀ + k) := by
          rw [hF k hk, Nat.zero_div, Nat.add_zero]
          exact (hi.pre.wordAt_eq (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact table_sub_scr hfit⟩) hw)
        rw [← hw', show s₃.mem = s₁.mem from hm₃]
        exact E₁
      · refine (hi.ent i (by omega_arith)).congr fun j hj => ?_
        rw [hm₃]
        exact entryW_frame hfit f₁ (by omega_arith) (by omega_arith) he hj
    · rw [hm₃]
      exact hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact entry_sub_table hfit (by omega_arith)⟩)
    · rw [o₃ r (fun h => h1 (by rw [h]; decide)), o₂ r (fun h => h1 (by rw [h]; decide)), o₁ r h1 h2,
        hi.regs r h1 h2]
  have hz : s₃.z = decide (N - (k + 1) = 0) := by
    rw [show s₃.z = (subFlags s₂ (s₂.gpr .lr) 1).z from rfl, subFlags_z, ht₂,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega_arith),
      Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this; simp at this; omega_arith
    · intro h; rw [show N - k - 1 = 0 by omega_arith]; rfl
  by_cases hl : k + 1 = N
  · refine .inl ⟨(eval_ne s₃).trans (by rw [hz]; simp; omega_arith),
      by rw [show k + 1 = N from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_ne s₃).trans (by rw [hz]; simp; omega_arith), N - (k + 1), by omega_arith, k + 1, rfl,
      by omega_arith, hinv⟩

/-! ## The tables -/

/-- What the table's construction leaves: entry `i` holds word `perm i` of the schedule. -/
structure KeysPost (s₀ : State) (b sched : BitVec 32) (g : Nat) (perm : Nat → Nat) (s : State) : Prop where
  pre : KeyPre s b sched
  ent : ∀ i < 8 * g + 2,
    EntryOk s.mem b i (Spec.Camellia.wordAt s₀.mem (State.addr sched + BitVec.ofNat 64 (8 * perm i)))
  frame : Frame [tableRegion b] s₀.mem s.mem
  regs : ∀ r, r ∉ keyWrites → r ≠ kp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  kpos : AtEntry s b (8 * g + 2)

theorem add8 (x : BitVec 32) {w : Nat} :
    x + BitVec.ofNat 32 (8 * w) + 8 = x + BitVec.ofNat 32 (8 * (w + 1)) := by
  rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, add_ofNat_ofNat, show 8 * w + 8 = 8 * (w + 1) by omega_arith]

theorem sub8 (x : BitVec 32) {w : Nat} :
    x + BitVec.ofNat 32 (8 * (w + 1)) - 8 = x + BitVec.ofNat 32 (8 * w) := by
  rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, BitVec.sub_eq_add_neg, BitVec.add_assoc,
    ← BitVec.sub_eq_add_neg, VG.Offset.ofNat_sub_ofNat (by omega_arith), show 8 * (w + 1) - 8 = 8 * w by omega_arith]

/-- `add r12, r12, #8` or `sub r12, r12, #8`. -/
theorem stepR12_ok (s : State) (op : DpOp) (hop : op = .add ∨ op = .sub) :
    ∃ s', runBlock isa [.dp op .r12 .r12 (.imm 8)] s = some s' ∧
      s'.gpr .r12 = (if op = .add then s.gpr .r12 + 8 else s.gpr .r12 - 8) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rcases hop with rfl | rfl
  · exact ⟨s.setReg .r12 (s.gpr .r12 + 8), by
      simp only [runBlock_cons, exec, Op2.eval, show encodable 8 = true by decide, ↓reduceIte, Option.map_some,
        runStep_some, runBlock_nil], by simp [RegUpd.gpr_setReg_self], fun r h => RegUpd.gpr_setReg_of_ne _ _ h,
      rfl, rfl, rfl⟩
  · exact ⟨s.setReg .r12 (s.gpr .r12 - 8), by
      simp only [runBlock_cons, exec, Op2.eval, show encodable 8 = true by decide, ↓reduceIte, Option.map_some,
        runStep_some, runBlock_nil], by simp [RegUpd.gpr_setReg_self], fun r h => RegUpd.gpr_setReg_of_ne _ _ h,
      rfl, rfl, rfl⟩

theorem exec_movImm {s : State} {d : Reg} {v : BitVec 32} (he : encodable v = true) :
    exec (.mov d (.imm v)) s = some (s.setReg d v) := by
  simp only [exec, Op2.eval, he, ↓reduceIte, Option.map_some]

theorem encKeys_wp {s₀ : State} {b sched : BitVec 32} {g : Nat} (hg : g = 3 ∨ g = 4) (hk : KeyPre s₀ b sched)
    (hr : s₀.gpr u7 = sched) (hl : s₀.gpr .lr = BitVec.ofNat 32 (8 * g + 2)) :
    WP isa encKeys s₀ (KeysPost s₀ b sched g id) := by
  have hg4 : g ≤ 4 := by omega_arith
  let s₂ := s₀.setReg kp (s₀.gpr sb + BitVec.ofNat 32 (4 * keySlot))
  have e₂ : runBlock isa tableSetup s₀ = some s₂ := by
    rw [tableSetup, runBlock_cons, slotAddr,
      exec_addImm (v := BitVec.ofNat 32 (4 * keySlot)) (by decide), runStep_some, runBlock_nil]
  unfold encKeys
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  have hinv : KeyInv s₀ b sched 0 (8 * g + 2) id (fun i => Spec.Camellia.wordAt s₀.mem
      (State.addr sched + BitVec.ofNat 64 (8 * i))) 0 s₂ := by
    refine ⟨hk.congr ?_ rfl rfl, ?_, ?_, ?_, fun i hi => by omega_arith, Frame.refl _ _, fun r h1 h2 => ?_, rfl, rfl⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]
    · rw [AtEntry, RegUpd.gpr_setReg_self, hk.base]; rfl
    · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hr]
      simp
    · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hl, Nat.sub_zero]
    · rw [RegUpd.gpr_setReg_of_ne _ _ h2]
  refine WP.mono (keyLoop_wp (e₀ := 0) (N := 8 * g + 2) (wk := id) (f := fun x => x + 8)
    (fun s => by
      obtain ⟨s', e', r', o', m', rd', wr'⟩ := stepR12_ok s .add (.inl rfl)
      exact ⟨s', e', by simpa using r', o', m', rd', wr'⟩) (by omega_arith) (by omega_arith) (fun k hk => by simp; omega_arith)
    (fun k _ => add8 sched) (fun k _ => by simp) (by omega_arith) hinv) fun s h => ?_
  exact ⟨h.pre, fun i hi => h.ent i (by omega_arith), h.frame, h.regs, h.rd, h.wr, by
    have := h.kpos; rwa [Nat.zero_add] at this⟩

/-- `keyOne_step` within the construction of a table from `s₀`. -/
theorem keyOne_inv {s₀ s : State} {b sched : BitVec 32} {d e w : Nat} (hd : d = 0 ∨ d = 8)
    (hk : KeyPre s b sched) (hkp : AtEntry s b e) (he : e < 34)
    (hr : s.gpr u7 = sched + BitVec.ofNat 32 (8 * w)) (hw : w + d / 8 < 34)
    (hf : Frame [tableRegion b] s₀.mem s.mem) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧ KeyPre s' b sched ∧ AtEntry s' b (e + 1) ∧
      (∀ r, r ∉ keyWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.gpr u7 = s.gpr u7 ∧
      s'.gpr .lr = s.gpr .lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [tableRegion b] s₀.mem s'.mem ∧
      EntryOk s'.mem b e (Spec.Camellia.wordAt s₀.mem (State.addr sched + BitVec.ofNat 64 (8 * (w + d / 8)))) ∧
      (∀ i < 34, i ≠ e → ∀ j < 16, entryW s'.mem b i j = entryW s.mem b i j) := by
  have hfit := hk.scr.fit
  obtain ⟨s', e', k', o', u', l', rd', wr', f', E'⟩ := keyOne_step hd hk hr hw hkp he
  refine ⟨s', e', hk.congr (o' _ (by decide) (by decide)) rd' wr', k', o', u', l', rd', wr', ?_, ?_,
    fun i hi hie j hj => entryW_frame hfit f' hi he hie hj⟩
  · exact hf.trans (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact entry_sub_table hfit he⟩)
  · rw [← hk.wordAt_eq (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact table_sub_scr hfit⟩) hw]
    exact E'

theorem decKeys_wp {s₀ : State} {b sched : BitVec 32} {g : Nat} (hg : g = 3 ∨ g = 4) (hk : KeyPre s₀ b sched)
    (hr : s₀.gpr u7 = sched + BitVec.ofNat 32 (8 * (8 * g))) (hl : s₀.gpr .lr = BitVec.ofNat 32 (8 * g - 2)) :
    WP isa decKeys s₀ (KeysPost s₀ b sched g (Camellia.decPerm g)) := by
  have hg4 : g ≤ 4 := by omega_arith
  have hg3 : 3 ≤ g := by omega_arith
  unfold decKeys
  -- `kw3`, `kw4` to entries 0 and 1.
  let s₂ := s₀.setReg kp (s₀.gpr sb + BitVec.ofNat 32 (4 * keySlot))
  have e₂ : runBlock isa tableSetup s₀ = some s₂ := by
    rw [tableSetup, runBlock_cons, slotAddr,
      exec_addImm (v := BitVec.ofNat 32 (4 * keySlot)) (by decide), runStep_some, runBlock_nil]
  have hk₂ : KeyPre s₂ b sched := hk.congr (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]) rfl rfl
  have hkp₂ : AtEntry s₂ b 0 := by
    rw [AtEntry, RegUpd.gpr_setReg_self, hk.base]; rfl
  have hr₂ : s₂.gpr u7 = sched + BitVec.ofNat 32 (8 * (8 * g)) := by
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hr]
  obtain ⟨s₃, e₃, hk₃, kp₃, o₃, u₃, l₃, rd₃, wr₃, hf₃, E₃, -⟩ :=
    keyOne_inv (s₀ := s₀) (d := 0) (Or.inl rfl) hk₂ hkp₂ (by omega_arith) hr₂ (by omega_arith) (Frame.refl _ _)
  obtain ⟨s₄, e₄, hk₄, kp₄, o₄, u₄, l₄, rd₄, wr₄, hf₄, E₄, P₄⟩ :=
    keyOne_inv (s₀ := s₀) (d := 8) (Or.inr rfl) hk₃ kp₃ (by omega_arith) (by rw [u₃, hr₂]) (by omega_arith) hf₃
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := stepR12_ok s₄ .sub (.inr rfl)
  have hr₆ : s₆.gpr u7 = sched + BitVec.ofNat 32 (8 * (8 * g - 1)) := by
    rw [show u7 = Reg.r12 from rfl, r₆]
    simp only [show (Reg.r12) = u7 from rfl, u₄, u₃, hr₂]
    have := sub8 sched (w := 8 * g - 1)
    rwa [show 8 * g - 1 + 1 = 8 * g by omega_arith] at this
  have hl₆ : s₆.gpr .lr = BitVec.ofNat 32 (8 * g - 2) := by
    rw [o₆ _ (by decide), l₄, l₃, RegUpd.gpr_setReg_of_ne _ _ (by decide), hl]
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [runBlock_app, runBlock_app, runBlock_app, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some, e₆], ?_⟩)
  -- The loop: entries 2 to `8 g - 1`.
  let F : Nat → BitVec 64 := fun i =>
    Spec.Camellia.wordAt s₀.mem (State.addr sched + BitVec.ofNat 64 (8 * Camellia.decPerm g i))
  have hF0 : F 0 = Spec.Camellia.wordAt s₀.mem (State.addr sched + BitVec.ofNat 64 (8 * (8 * g + 0 / 8))) := by
    simp [F, Camellia.decPerm]
  have hF1 : F 1 = Spec.Camellia.wordAt s₀.mem (State.addr sched + BitVec.ofNat 64 (8 * (8 * g + 8 / 8))) := by
    simp [F, Camellia.decPerm]
  have hm₆ : s₆.mem = s₄.mem := m₆
  have hinv : KeyInv s₀ b sched 2 (8 * g - 2) (fun k => 8 * g - 1 - k) F 0 s₆ := by
    refine ⟨hk₄.congr ?_ ?_ ?_, ?_, by rw [hr₆, Nat.sub_zero], by rw [hl₆, Nat.sub_zero],
      fun i hi => ?_, by rw [hm₆]; exact hf₄, fun r h1 h2 => ?_, by rw [rd₆, rd₄, rd₃]; rfl,
      by rw [wr₆, wr₄, wr₃]; rfl⟩
    · rw [o₆ _ (by decide)]
    · rw [rd₆]
    · rw [wr₆]
    · rw [AtEntry, o₆ _ (by decide)]; exact kp₄
    · rw [hm₆]
      rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl
      · rw [hF0]; exact E₃.congr fun j hj => P₄ 0 (by omega_arith) (by omega_arith) j hj
      · rw [hF1]; exact E₄
    · rw [o₆ r (fun h => h1 (by rw [h]; decide)), o₄ r h1 h2, o₃ r h1 h2, RegUpd.gpr_setReg_of_ne _ _ h2]
  refine WP.seq (WP.mono (keyLoop_wp (e₀ := 2) (N := 8 * g - 2) (wk := fun k => 8 * g - 1 - k)
    (f := fun x => x - 8) (fun s => by
      obtain ⟨s', e', r', o', m', rd', wr'⟩ := stepR12_ok s .sub (.inr rfl)
      exact ⟨s', e', by simpa using r', o', m', rd', wr'⟩) (by omega_arith) (by omega_arith)
    (fun k hk => by omega_arith) (fun k hk => ?_) (fun k hk => ?_) (by omega_arith) hinv) fun s h => ?_)
  · have := sub8 sched (w := 8 * g - 1 - (k + 1))
    rwa [show 8 * g - 1 - (k + 1) + 1 = 8 * g - 1 - k by omega_arith] at this
  · simp only [F, Camellia.decPerm, show ¬ 2 + k < 2 by omega_arith, show 2 + k < 8 * g by omega_arith, ↓reduceIte,
      show 8 * g + 1 - (2 + k) = 8 * g - 1 - k by omega_arith]
  -- `kw1`, `kw2` to entries `8 g` and `8 g + 1`.
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := stepR12_ok s .sub (.inr rfl)
  have hr₇ : s₇.gpr u7 = sched + BitVec.ofNat 32 (8 * 0) := by
    rw [show u7 = Reg.r12 from rfl, r₇]
    simp only [show (Reg.r12) = u7 from rfl, h.r12, show 8 * g - 1 - (8 * g - 2) = 0 + 1 by omega_arith]
    exact sub8 sched
  have hk₇ : KeyPre s₇ b sched := h.pre.congr (o₇ _ (by decide)) rd₇ wr₇
  have hkp₇ : AtEntry s₇ b (8 * g) := by
    rw [AtEntry, o₇ _ (by decide)]
    have := h.kpos
    rwa [show 2 + (8 * g - 2) = 8 * g by omega_arith] at this
  obtain ⟨s₈, e₈, hk₈, kp₈, o₈, u₈, -, rd₈, wr₈, hf₈, E₈, P₈⟩ :=
    keyOne_inv (s₀ := s₀) (d := 0) (Or.inl rfl) hk₇ hkp₇ (by omega_arith) hr₇ (by omega_arith) (by rw [m₇]; exact h.frame)
  obtain ⟨s₉, e₉, hk₉, kp₉, o₉, -, -, rd₉, wr₉, hf₉, E₉, P₉⟩ :=
    keyOne_inv (s₀ := s₀) (d := 8) (Or.inr rfl) hk₈ kp₈ (by omega_arith) (by rw [u₈, hr₇]) (by omega_arith) hf₈
  refine WP.of_runBlock ⟨s₉, by
    rw [runBlock_app, runBlock_app, e₇, Option.bind_some, e₈, Option.bind_some, e₉],
    hk₉, fun i hi => ?_, hf₉, fun r h1 h2 => ?_, by rw [rd₉, rd₈, rd₇, h.rd], by rw [wr₉, wr₈, wr₇, h.wr],
    by have := kp₉; rwa [show 8 * g + 1 + 1 = 8 * g + 2 by omega_arith] at this⟩
  · rcases (show i < 8 * g ∨ i = 8 * g ∨ i = 8 * g + 1 by omega_arith) with hi' | rfl | rfl
    · refine (h.ent i (by omega_arith)).congr fun j hj => ?_
      rw [P₉ i (by omega_arith) (by omega_arith) j hj, P₈ i (by omega_arith) (by omega_arith) j hj, m₇]
    · have hp : Camellia.decPerm g (8 * g) = 0 + 0 / 8 := by
        unfold Camellia.decPerm
        simp only [show ¬ 8 * g < 2 by omega_arith, show ¬ 8 * g < 8 * g by omega_arith, ↓reduceIte]; omega_arith
      rw [hp]; exact E₈.congr fun j hj => P₉ _ (by omega_arith) (by omega_arith) j hj
    · have hp : Camellia.decPerm g (8 * g + 1) = 0 + 8 / 8 := by
        unfold Camellia.decPerm
        simp only [show ¬ 8 * g + 1 < 2 by omega_arith, show ¬ 8 * g + 1 < 8 * g by omega_arith, ↓reduceIte]; omega_arith
      rw [hp]; exact E₉
  · rw [o₉ r h1 h2, o₈ r h1 h2, o₇ r (fun h => h1 (by rw [h]; decide)), h.regs r h1 h2]

end VG.Proof.Camellia.Arm
