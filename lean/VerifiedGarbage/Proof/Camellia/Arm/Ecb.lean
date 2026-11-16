module

public import VerifiedGarbage.Proof.Camellia.Arm.Prologue
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Camellia.Arm.Core
import VerifiedGarbage.Proof.Camellia.Arm.Crypt8
import VerifiedGarbage.Proof.Camellia.Arm.Fl
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Camellia.Arm.Copy

/-! ### `Camellia.Arm.Group`, which only this module used -/

section

/-! ### `Camellia.Arm.Keys`, which only this module used -/

section

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
  obtain h5 : r ≠ q 5 := fun h => hr (by rw [h]; decide)
  obtain h11 : r ≠ t1 := fun h => hr (by rw [h]; decide)
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
  obtain hchk : check (lanes 32 10) entryCfg (linExt 0) (keyPlanes w) keyEnv
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
  obtain hkeep : ∀ r, r ∉ keyWrites → s'.gpr r = s.gpr r := fun r hr => o' r (keyPlanes_keep w hw r hr)
  obtain hkp : s'.gpr kp = s.gpr kp := hkeep _ (by decide)
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
  obtain hin₀ : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 d)) 4 := by
    rw [hr']; exact hk.word_in (by omega_arith)
  let s₁ := s.setReg (q 4) (s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 d)) 32)
  obtain e₁ : exec (.ldr (q 4) .r12 d) s = some s₁ := exec_ldr (by omega_arith) hin₀
  obtain k₁ := keeps_setReg s (s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 d)) 32)
    (d := q 4) (by decide) (by decide)
  obtain hs₁ : Scr s₁ b := ⟨by rw [k₁.wr]; exact hs.wr, hs.fit⟩
  obtain ⟨s₂, e₂, p₂, o₂, g₂, u₂, l₂, q₂, rd₂, wr₂, f₂⟩ := keyPlanes_step (w := 0) (e := e) hs₁
    (by rw [AtEntry, k₁.gpr _ (by decide)]; exact hkp) he (.inl rfl)
  -- The second word.
  obtain hr₂ : s₂.gpr .r12 = s.gpr .r12 := by rw [show (Reg.r12) = u7 from rfl, u₂, k₁.gpr _ (by decide)]
  obtain hin₄ : InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (d + 4))) 4 := by
    rw [hr₂, hr', rd₂, wr₂, k₁.rd, k₁.wr]; exact hk.word_in (by omega_arith)
  obtain hm₂ : s₂.mem.readW (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (d + 4))) 32 =
      s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 (d + 4))) 32 := by
    rw [hr₂, ← k₁.mem]
    refine f₂.readW (r := ⟨State.addr sched, 272⟩) ?_ (fun r hr' => ?_) (by decide)
    · rw [hr', KeyPre.addr hk.schFit (by omega_arith)]
      exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr'; subst hr'
      exact hk.entry_sep he
  let s₃ := s₂.setReg (q 4) (s₂.mem.readW (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (d + 4))) 32)
  obtain e₃ : exec (.ldr (q 4) .r12 (d + 4)) s₂ = some s₃ := exec_ldr (by omega_arith) hin₄
  obtain k₃ := keeps_setReg s₂ (s₂.mem.readW (State.addr (s₂.gpr .r12 + BitVec.ofNat 32 (d + 4))) 32)
    (d := q 4) (by decide) (by decide)
  obtain hs₃ : Scr s₃ b := ⟨by rw [k₃.wr, wr₂, k₁.wr]; exact hs.wr, hs.fit⟩
  obtain hkp₃ : AtEntry s₃ b e := by
    rw [AtEntry, k₃.gpr _ (by decide), g₂ _ (by decide), k₁.gpr _ (by decide)]; exact hkp
  obtain ⟨s₄, e₄, p₄, o₄, g₄, u₄, l₄, q₄, rd₄, wr₄, f₄⟩ := keyPlanes_step (w := 1) (e := e) hs₃ hkp₃ he (.inr rfl)
  -- `kp += 64`.
  obtain hkp₄ : s₄.gpr kp = s.gpr kp := by
    rw [g₄ _ (by decide), k₃.gpr _ (by decide), g₂ _ (by decide), k₁.gpr _ (by decide)]
  obtain hrd : s₄.rd = s.rd := by rw [rd₄, k₃.rd, rd₂, k₁.rd]
  obtain hwr : s₄.wr = s.wr := by rw [wr₄, k₃.wr, wr₂, k₁.wr]
  obtain hw4 : 8 * w + d + 8 ≤ 272 := by omega_arith
  obtain hent : ∀ v < 2, ∀ j < 8, ∀ p < 32, (entryW s₄.mem b e (8 * v + j)).getLsbD p =
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
  obtain hw := hwk k hk
  obtain ⟨s₁, e₁, kp₁, o₁, u₁, l₁, rd₁, wr₁, f₁, E₁⟩ := keyOne_step (d := 0) (e := e₀ + k) (Or.inl rfl)
    hi.pre hi.r12 (by omega_arith) hi.kpos (by omega_arith)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := hop s₁
  obtain e₃ := subs_lr s₂
  let s₃ := (subFlags s₂ (s₂.gpr .lr) 1).setReg .lr (s₂.gpr .lr - 1)
  obtain o₃ : ∀ r, r ≠ .lr → s₃.gpr r = s₂.gpr r := fun r h => by
    rw [RegUpd.gpr_setReg_of_ne _ _ h, subFlags_gpr]
  refine WP.of_runBlock ⟨s₃, by
    rw [runBlock_app, e₁, Option.bind_some,
      show ([i₁, .subs .lr .lr (.imm 1)] : List Instr) = [i₁] ++ [.subs .lr .lr (.imm 1)] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃], ?_⟩
  obtain ht₂ : s₂.gpr .lr = BitVec.ofNat 32 (N - k) := by rw [o₂ _ (by decide), l₁, hi.cnt]
  obtain hc₃ : s₃.gpr .lr = BitVec.ofNat 32 (N - (k + 1)) := by
    rw [RegUpd.gpr_setReg_self, ht₂, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show N - k - 1 = N - (k + 1) by omega_arith]
  obtain hm₃ : s₃.mem = s₁.mem := by rw [RegUpd.mem_setReg, subFlags_mem, m₂]
  obtain hinv : KeyInv s₀ b sched e₀ N wk F (k + 1) s₃ := by
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
        obtain hw' : Spec.Camellia.wordAt s.mem (State.addr sched + BitVec.ofNat 64 (8 * (wk k + 0 / 8))) =
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
  obtain hz : s₃.z = decide (N - (k + 1) = 0) := by
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
  obtain hg4 : g ≤ 4 := by omega_arith
  let s₂ := s₀.setReg kp (s₀.gpr sb + BitVec.ofNat 32 (4 * keySlot))
  obtain e₂ : runBlock isa tableSetup s₀ = some s₂ := by
    rw [tableSetup, runBlock_cons, slotAddr,
      exec_addImm (v := BitVec.ofNat 32 (4 * keySlot)) (by decide), runStep_some, runBlock_nil]
  unfold encKeys
  refine WP.seq (WP.of_runBlock ⟨s₂, e₂, ?_⟩)
  obtain hinv : KeyInv s₀ b sched 0 (8 * g + 2) id (fun i => Spec.Camellia.wordAt s₀.mem
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
  obtain hg4 : g ≤ 4 := by omega_arith
  obtain hg3 : 3 ≤ g := by omega_arith
  unfold decKeys
  -- `kw3`, `kw4` to entries 0 and 1.
  let s₂ := s₀.setReg kp (s₀.gpr sb + BitVec.ofNat 32 (4 * keySlot))
  obtain e₂ : runBlock isa tableSetup s₀ = some s₂ := by
    rw [tableSetup, runBlock_cons, slotAddr,
      exec_addImm (v := BitVec.ofNat 32 (4 * keySlot)) (by decide), runStep_some, runBlock_nil]
  obtain hk₂ : KeyPre s₂ b sched := hk.congr (by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]) rfl rfl
  obtain hkp₂ : AtEntry s₂ b 0 := by
    rw [AtEntry, RegUpd.gpr_setReg_self, hk.base]; rfl
  obtain hr₂ : s₂.gpr u7 = sched + BitVec.ofNat 32 (8 * (8 * g)) := by
    rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hr]
  obtain ⟨s₃, e₃, hk₃, kp₃, o₃, u₃, l₃, rd₃, wr₃, hf₃, E₃, -⟩ :=
    keyOne_inv (s₀ := s₀) (d := 0) (Or.inl rfl) hk₂ hkp₂ (by omega_arith) hr₂ (by omega_arith) (Frame.refl _ _)
  obtain ⟨s₄, e₄, hk₄, kp₄, o₄, u₄, l₄, rd₄, wr₄, hf₄, E₄, P₄⟩ :=
    keyOne_inv (s₀ := s₀) (d := 8) (Or.inr rfl) hk₃ kp₃ (by omega_arith) (by rw [u₃, hr₂]) (by omega_arith) hf₃
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := stepR12_ok s₄ .sub (.inr rfl)
  obtain hr₆ : s₆.gpr u7 = sched + BitVec.ofNat 32 (8 * (8 * g - 1)) := by
    rw [show u7 = Reg.r12 from rfl, r₆]
    simp only [show (Reg.r12) = u7 from rfl, u₄, u₃, hr₂]
    have := sub8 sched (w := 8 * g - 1)
    rwa [show 8 * g - 1 + 1 = 8 * g by omega_arith] at this
  obtain hl₆ : s₆.gpr .lr = BitVec.ofNat 32 (8 * g - 2) := by
    rw [o₆ _ (by decide), l₄, l₃, RegUpd.gpr_setReg_of_ne _ _ (by decide), hl]
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [runBlock_app, runBlock_app, runBlock_app, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some, e₆], ?_⟩)
  -- The loop: entries 2 to `8 g - 1`.
  let F : Nat → BitVec 64 := fun i =>
    Spec.Camellia.wordAt s₀.mem (State.addr sched + BitVec.ofNat 64 (8 * Camellia.decPerm g i))
  obtain hF0 : F 0 = Spec.Camellia.wordAt s₀.mem (State.addr sched + BitVec.ofNat 64 (8 * (8 * g + 0 / 8))) := by
    simp [F, Camellia.decPerm]
  obtain hF1 : F 1 = Spec.Camellia.wordAt s₀.mem (State.addr sched + BitVec.ofNat 64 (8 * (8 * g + 8 / 8))) := by
    simp [F, Camellia.decPerm]
  have hm₆ : s₆.mem = s₄.mem := m₆
  obtain hinv : KeyInv s₀ b sched 2 (8 * g - 2) (fun k => 8 * g - 1 - k) F 0 s₆ := by
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
  obtain hr₇ : s₇.gpr u7 = sched + BitVec.ofNat 32 (8 * 0) := by
    rw [show u7 = Reg.r12 from rfl, r₇]
    simp only [show (Reg.r12) = u7 from rfl, h.r12, show 8 * g - 1 - (8 * g - 2) = 0 + 1 by omega_arith]
    exact sub8 sched
  obtain hk₇ : KeyPre s₇ b sched := h.pre.congr (o₇ _ (by decide)) rd₇ wr₇
  obtain hkp₇ : AtEntry s₇ b (8 * g) := by
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

end

end


/-!
# A group of blocks of Camellia ECB on ARMv7

As SM4's (`Proof/Sm4/Arm/Group.lean`): `dataGroup_wp`, one iteration of the
data loop, copies the group's blocks (eight, or the last one to seven) to
the tail buffer, transforms it (`crypt8_ok`), copies the blocks back and
steps to the next group. The data pointer and the blocks left live in their
slots (`dSlot`, `nSlot`) between the steps, which use every other register.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Proof.Camellia (DInv outF not_contains_off blockAt_getD cryptWords)
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR lsrOp ldS stS)

/-! ## The scratch buffer's contents -/

/-- The slots `lo … hi - 1` of the scratch buffer at `b`. -/
abbrev slotsRegion (b : BitVec 32) (lo hi : Nat) : Region :=
  ⟨State.addr b + BitVec.ofNat 64 (4 * lo), 4 * (hi - lo)⟩

/-- A slot outside a frame. -/
theorem slot_keep {rs : List Region} {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {lo hi : Nat} (hhi : hi ≤ slots) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotsRegion b lo hi).Disjoint r)
    {k : Nat} (hk1 : lo ≤ k) (hk2 : k < hi) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [slots_eq] at hfit hhi
  rw [slot_addr (by omega_arith)]
  exact hf.readW (VG.Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)) hd (by decide)

/-- What the data loop keeps in the scratch buffer: the table and the saved
registers. -/
structure ScrOk (s₀ : State) (b : BitVec 32) (g : Nat) (E : Nat → BitVec 64) (m : Mem) : Prop where
  keys : ∀ e < 8 * g + 2, EntryOk m b e (E e)
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads are outside the regions. -/
def KeepOut (b : BitVec 32) (rs : List Region) : Prop :=
  ∀ r ∈ rs, (slotsRegion b keySlot grpSlot).Disjoint r ∧ (slotsRegion b savedSlot dSlot).Disjoint r

theorem ScrOk.frame {s₀ : State} {b : BitVec 32} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g = 3 ∨ g = 4) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {rs : List Region}
    (hf : Frame rs m m') (hd : KeepOut b rs) : ScrOk s₀ b g E m' := by
  refine ⟨fun e he => (h.keys e he).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact slot_keep hfit (by decide) hf (fun r hr => (hd r hr).1) (by omega_arith)
      (by rw [grpSlot_eq, keySlot_eq]; rcases hg with rfl | rfl <;> omega_arith)
  · rw [← h.saved i hi]
    exact slot_keep hfit (by decide) hf (fun r hr => (hd r hr).2) (by omega_arith)
      (by rw [savedSlot_eq, dSlot_eq]; omega_arith)

/-! ## The data loop -/

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : BitVec 32) (n : Nat) : Prop where
  scr : ScrIn s₀.wr b
  dat : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨State.addr D, 16 * n⟩ ⟨State.addr b, 4 * slots⟩
  fitD : D.toNat + 16 * n ≤ 2 ^ 32

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : BitVec 32) (n : Nat) (g : Nat) (E : Nat → BitVec 64) (k : Nat) (s : State) :
    Prop where
  base : s.gpr sb = b
  dp : s.gpr .r1 = D + BitVec.ofNat 32 (128 * k)
  np : s.gpr .r2 = BitVec.ofNat 32 (n - 8 * k)
  lt : 8 * k < n
  lr : s.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g)
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n (8 * k) (outF s₀.mem (State.addr D) g E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : BitVec 32) (n : Nat) (g : Nat) (E : Nat → BitVec 64) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem (State.addr D) n n (outF s₀.mem (State.addr D) g E)
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem KeepOut.cons {b : BitVec 32} {r : Region} {rs : List Region} (h₁ : KeepOut b [r]) (h₂ : KeepOut b rs) :
    KeepOut b (r :: rs) := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h₁ _ List.mem_cons_self
  · exact h₂ x hx

theorem KeepOut.nil (b : BitVec 32) : KeepOut b [] := fun _ h => absurd h List.not_mem_nil

/-- A region at an offset of the scratch buffer, outside what `ScrOk` reads. -/
theorem keepOut_off (b : BitVec 32) {e n : Nat} (hn : e + n ≤ 4 * slots)
    (h1 : e + n ≤ 4 * keySlot ∨ 4 * grpSlot ≤ e) (h2 : e + n ≤ 4 * savedSlot ∨ 4 * dSlot ≤ e) :
    KeepOut b [⟨State.addr b + BitVec.ofNat 64 e, n⟩] := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [slots_eq] at hn
  rw [keySlot_eq, grpSlot_eq] at h1
  rw [savedSlot_eq, dSlot_eq] at h2
  exact ⟨VG.Offset.disjoint _ (by rw [keySlot_eq, grpSlot_eq]; omega_arith) (by rw [keySlot_eq, grpSlot_eq]; omega_arith)
      (by omega_arith),
    VG.Offset.disjoint _ (by rw [savedSlot_eq, dSlot_eq]; omega_arith) (by rw [savedSlot_eq, dSlot_eq]; omega_arith) (by omega_arith)⟩

/-- A region outside the scratch buffer. -/
theorem keepOut_out (b : BitVec 32) {R : Region}
    (h : Region.Disjoint R ⟨State.addr b, 4 * slots⟩) : KeepOut b [R] := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨(h.sub_right (VG.Offset.sub_base _ (by rw [slots_eq, keySlot_eq, grpSlot_eq]; omega_arith))).symm,
    (h.sub_right (VG.Offset.sub_base _ (by rw [slots_eq, savedSlot_eq, dSlot_eq]; omega_arith))).symm⟩

theorem keepOut_ctx {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) : KeepOut b (ctxRegions b) := by
  obtain hb := addr_toNat b
  have h2 := hfit
  rw [slots_eq] at h2
  refine KeepOut.cons ?_ (KeepOut.cons ?_ (KeepOut.cons ?_ (KeepOut.nil b)))
  · have := keepOut_off b (e := 0) (n := 4 * keySlot) (by rw [slots_eq, keySlot_eq] <;> omega_arith)
      (.inl (by omega_arith)) (.inl (by rw [keySlot_eq, savedSlot_eq] <;> omega_arith))
    simpa using this
  · rw [VG.Arm.addr_add (by rw [grpSlot_eq] <;> omega_arith)]
    exact keepOut_off b (by rw [grpSlot_eq, slots_eq] <;> omega_arith) (.inr (Nat.le_refl _))
      (.inl (by rw [grpSlot_eq, savedSlot_eq] <;> omega_arith))
  · rw [VG.Arm.addr_add (by rw [tailSlot_eq] <;> omega_arith)]
    exact keepOut_off b (by rw [tailSlot_eq, slots_eq] <;> omega_arith) (.inr (by rw [tailSlot_eq, grpSlot_eq] <;> omega_arith))
      (.inr (by rw [tailSlot_eq, dSlot_eq] <;> omega_arith))

theorem dataGroup_wp {s₀ : State} {b D : BitVec 32} {n : Nat} {g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n)
    (hg : g = 3 ∨ g = 4) {k : Nat} {s : State} (hi : GInv s₀ b D n g E k s) :
    WP isa Impl.Camellia.Arm.group s fun s' => (s'.z = true ∧ GDone s₀ b D n g E s') ∨
      (s'.z = false ∧ GInv s₀ b D n g E (k + 1) s') := by
  -- Facts are stated with `obtain`, not `have`: `have` keeps its proof in the context (a `let` nothing
  -- unfolds), and every `(by …)` in a term first instantiates and shares the whole context (`Term.runTactic`).
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hb := addr_toNat b
  rw [slots_eq] at hfit
  obtain hfit' : b.toNat + 4 * slots ≤ 2 ^ 32 := by rw [slots_eq]; omega_arith
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 32 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 32 (128 * k)
  let T := b + BitVec.ofNat 32 (4 * tailSlot)
  obtain hA : State.addr A = State.addr D + BitVec.ofNat 64 (128 * k) := VG.Arm.addr_add (by omega_arith)
  obtain hT : State.addr T = State.addr b + BitVec.ofNat 64 (4 * tailSlot) := VG.Arm.addr_add (by rw [tailSlot_eq]; omega_arith)
  obtain hAn : A.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_arith)]; omega_arith
  obtain hTn : T.toNat + 16 * c ≤ 2 ^ 32 := by rw [toNat_add32 _ (by rw [tailSlot_eq]; omega_arith), tailSlot_eq]; omega_arith
  obtain hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr T + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwS.mem, ?_⟩
    rw [hT, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t < 16 * c, t % 4 = 0 → InRegions s.wr (State.addr A + BitVec.ofNat 64 t) 4 := by
    intro t ht h4
    refine ⟨_, hwD, ?_⟩
    rw [hA, VG.Offset.add_add]
    exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain subA : Region.Sub ⟨State.addr A, 16 * c⟩ ⟨State.addr D, 16 * n⟩ := by
    rw [hA]; exact VG.Offset.sub_base _ (by omega_arith)
  obtain subT : Region.Sub ⟨State.addr T, 16 * c⟩ ⟨State.addr b, 4 * slots⟩ := by
    rw [hT]; exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq]; omega_arith)
  obtain sepAT : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr T, 16 * c⟩ :=
    (hp.sep.sub_left subA).sub_right subT
  obtain dD : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨State.addr b, 4 * slots⟩) →
      ∀ r ∈ rs, Region.Disjoint ⟨State.addr D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
  obtain koT : KeepOut b [⟨State.addr T, 16 * c⟩] := by
    rw [hT]; exact keepOut_off b (by rw [slots_eq, tailSlot_eq]; omega_arith)
      (.inr (by rw [tailSlot_eq, grpSlot_eq]; omega_arith)) (.inr (by rw [tailSlot_eq, dSlot_eq]; omega_arith))
  obtain koA : KeepOut b [⟨State.addr A, 16 * c⟩] := keepOut_out b (hp.sep.sub_left subA)
  have r1₀ : s.gpr .r1 = A := hi.dp
  unfold Impl.Camellia.Arm.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.np hv) fun s₁ ⟨r3₁, o₁, m₁, rd₁, wr₁, sp₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a, sp₂a⟩ := movR_ok s₁ .r0 .r1
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₂a .r12 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₂ r h12, o₂a r h0, o₁ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [show ([movR .r0 .r1, slotAddr .r12 tailSlot] : List Instr) = [movR .r0 .r1] ++ [slotAddr .r12 tailSlot] from rfl,
      runBlock_app, e₂a, Option.bind_some]; exact e₂, ?_⟩)
  refine WP.mono (copyBlocks_wp (A := A) (B := T) hc0 hc8 hAn hTn
    (fun t ht h4 => by rw [rd₂', wr₂']; exact inRd (inA t ht h4))
    (fun t ht h4 => by rw [wr₂']; exact inT t ht h4) sepAT
    ⟨by rw [o₂ _ (by decide), r₂a, o₁ _ (by decide) (by decide), r1₀]; simp [A],
      by rw [r₂, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base]; simp [T],
      by rw [o₂ _ (by decide), o₂a _ (by decide), r3₁, Nat.sub_zero], ⟨fun t ht => by omega_arith, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₃ h₃ => ?_
  obtain f₃ : Frame [⟨State.addr T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact h₃.cp.frame
  obtain g₃ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₃.gpr r = s.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₃.regs r h0 h12 h3 h4, g₂ r h0 h12 h3 h4]
  obtain base₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b g E s₃.mem := hi.scr.frame hg hfit' f₃ koT
  obtain wr₃ : s₃.wr = s.wr := by rw [h₃.wr, wr₂']
  obtain rd₃ : s₃.rd = s.rd := by rw [h₃.rd, rd₂']
  obtain sp₃ : s₃.sp = s.sp := by rw [h₃.sp, sp₂, sp₂a, sp₁]
  obtain hwS₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hwS
  -- The data pointer, the blocks left and the postwhitening's address to their slots.
  unfold cryptSaved
  obtain ⟨s₄a, e₄a, m₄a, g₄a, rd₄a, wr₄a, sp₄a, -, f₄a⟩ := stSlot_ok s₃ .r1 sb (k := dSlot) base₃ (by decide) hwS₃
  obtain ⟨s₄b, e₄b, m₄b, g₄b, rd₄b, wr₄b, sp₄b, -, f₄b⟩ := stSlot_ok s₄a .r2 sb (k := nSlot)
    (by rw [g₄a, base₃]) (by decide) (by rw [wr₄a]; exact hwS₃)
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄, sp₄, -, f₄⟩ := stSlot_ok s₄b .lr sb (k := endSlot)
    (by rw [g₄b, g₄a, base₃]) (by decide) (by rw [wr₄b, wr₄a]; exact hwS₃)
  obtain r1₃ : s₃.gpr .r1 = A := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), r1₀]
  obtain r2₃ : s₃.gpr .r2 = BitVec.ofNat 32 v := by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.np]
  obtain lr₃ : s₃.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) := by
    rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hi.lr]
  obtain fs : Frame [⟨wordAddr b dSlot, 4⟩, ⟨wordAddr b nSlot, 4⟩, ⟨wordAddr b endSlot, 4⟩] s₃.mem s₄.mem :=
    (f₄a.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      ((f₄b.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
        (f₄.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩))
  obtain hsub : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩, ⟨wordAddr b endSlot, 4⟩],
      Region.Sub r ⟨State.addr b, 4 * slots⟩ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_sub hfit' (by decide)
    · exact slot_sub hfit' (by decide)
    · exact slot_sub hfit' (by decide)
  obtain dsTab : KeepOut b [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩, ⟨wordAddr b endSlot, 4⟩] := by
    refine KeepOut.cons ?_ (KeepOut.cons ?_ (KeepOut.cons ?_ (KeepOut.nil b)))
    · rw [slot_addr (by rw [dSlot_eq]; omega_arith)]
      exact keepOut_off b (by rw [dSlot_eq, slots_eq]; omega_arith) (.inr (by rw [dSlot_eq, grpSlot_eq]; omega_arith))
        (.inr (Nat.le_refl _))
    · rw [slot_addr (by rw [nSlot_eq]; omega_arith)]
      exact keepOut_off b (by rw [nSlot_eq, slots_eq]; omega_arith) (.inr (by rw [nSlot_eq, grpSlot_eq]; omega_arith))
        (.inr (by rw [nSlot_eq, dSlot_eq]; omega_arith))
    · rw [slot_addr (by rw [endSlot_eq]; omega_arith)]
      exact keepOut_off b (by rw [endSlot_eq, slots_eq]; omega_arith) (.inr (by rw [endSlot_eq, grpSlot_eq]; omega_arith))
        (.inl (by rw [endSlot_eq, savedSlot_eq]))
  obtain sc₄ : ScrOk s₀ b g E s₄.mem := sc₃.frame hg hfit' fs dsTab
  obtain base₄ : s₄.gpr sb = b := by rw [g₄, g₄b, g₄a, base₃]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₄b, wr₄a, wr₃]
  obtain dp₄ : s₄.mem.readW (wordAddr b dSlot) 32 = A := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide), m₄b,
      readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide), m₄a,
      readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, r1₃]
  obtain np₄ : s₄.mem.readW (wordAddr b nSlot) 32 = BitVec.ofNat 32 v := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_right (by decide), m₄b,
      readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, g₄a, r2₃]
  obtain ep₄ : s₄.mem.readW (wordAddr b endSlot) 32 = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) := by
    rw [m₄, readW_slot_write hfit' _ (by decide) (by decide), ite_eq_left rfl, g₄b, g₄a, lr₃]
  refine WP.seq (WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([stS dSlot .r1, stS nSlot .r2, stS endSlot .lr] : List Instr) =
      [.str .r1 sb (4 * dSlot)] ++ ([.str .r2 sb (4 * nSlot)] ++ [.str .lr sb (4 * endSlot)]) from rfl,
      runBlock_app, e₄a, Option.bind_some, runBlock_app, e₄b, Option.bind_some, e₄],
    ?_⟩))
  -- The eight blocks.
  obtain hcore : CorePre s₄ g E :=
    { scr := ⟨by rw [base₄, wr₄']; exact hwS.mem, by rw [base₄]; exact hfit'⟩
      nk34 := by rcases hg with rfl | rfl <;> decide
      keys := fun e he => by rw [base₄]; exact sc₄.keys e he
      hg := hg
      bound := by rw [slotW, base₄]; exact ep₄ }
  refine WP.seq (WP.mono (WP.sp (crypt8_ok hcore)) fun s₅ ⟨⟨c₅, b₅⟩, sp₅'⟩ => ?_)
  obtain base₅ : s₅.gpr sb = b := by rw [c₅.base, base₄]
  obtain f₅ : Frame (ctxRegions b) s₄.mem s₅.mem := by have := c₅.frame; rw [base₄] at this; exact this
  obtain keep₅ : ∀ j, j = dSlot ∨ j = nSlot ∨ j = endSlot →
      s₅.mem.readW (wordAddr b j) 32 = s₄.mem.readW (wordAddr b j) 32 :=
    fun j hj => by
      have := c₅.slot (k := j) (by rw [base₄]; exact hfit') (by rcases hj with rfl | rfl | rfl <;> decide)
        (by rcases hj with rfl | rfl | rfl <;> decide) (by rcases hj with rfl | rfl | rfl <;> decide)
        (.inl (by rcases hj with rfl | rfl | rfl <;> decide))
      simp only [slotW, base₅, base₄] at this; exact this
  obtain sc₅ : ScrOk s₀ b g E s₅.mem := sc₄.frame hg hfit' f₅ (keepOut_ctx hfit')
  obtain wr₅ : s₅.wr = s.wr := by rw [c₅.wr, wr₄']
  obtain rd₅ : s₅.rd = s.rd := by rw [c₅.rd, rd₄, rd₄b, rd₄a, rd₃]
  obtain sp₅ : s₅.sp = s.sp := by rw [sp₅', sp₄, sp₄b, sp₄a, sp₃]
  obtain hwS₅ : ScrIn s₅.wr b := by rw [wr₅]; exact hwS
  -- The data pointer, the blocks left and the postwhitening's address back.
  obtain ⟨s₆a, e₆a, r₆a, o₆a, m₆a, rd₆a, wr₆a, sp₆a⟩ := ldSlot_ok s₅ .r1 sb (k := dSlot) base₅ (by decide) hwS₅
  obtain ⟨s₆b, e₆b, r₆b, o₆b, m₆b, rd₆b, wr₆b, sp₆b⟩ := ldSlot_ok s₆a .r2 sb (k := nSlot)
    (by rw [o₆a _ (by decide), base₅]) (by decide) (by rw [wr₆a]; exact hwS₅)
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := ldSlot_ok s₆b .lr sb (k := endSlot)
    (by rw [o₆b _ (by decide), o₆a _ (by decide), base₅]) (by decide) (by rw [wr₆b, wr₆a]; exact hwS₅)
  refine WP.of_runBlock ⟨s₆, by
    rw [show ([ldS .r1 dSlot, ldS .r2 nSlot, ldS .lr endSlot] : List Instr) =
      [.ldr .r1 sb (4 * dSlot)] ++ ([.ldr .r2 sb (4 * nSlot)] ++ [.ldr .lr sb (4 * endSlot)]) from rfl,
      runBlock_app, e₆a, Option.bind_some, runBlock_app, e₆b, Option.bind_some, e₆],
    ?_⟩
  obtain r1₆ : s₆.gpr .r1 = A := by rw [o₆ _ (by decide), o₆b _ (by decide), r₆a, keep₅ _ (by decide), dp₄]
  obtain r2₆ : s₆.gpr .r2 = BitVec.ofNat 32 v := by
    rw [o₆ _ (by decide), r₆b, m₆a, keep₅ _ (by decide), np₄]
  obtain lr₆ : s₆.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) := by
    rw [r₆, m₆b, m₆a, keep₅ _ (by decide), ep₄]
  obtain base₆ : s₆.gpr sb = b := by rw [o₆ _ (by decide), o₆b _ (by decide), o₆a _ (by decide), base₅]
  obtain mem₆ : s₆.mem = s₅.mem := by rw [m₆, m₆b, m₆a]
  obtain wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₆b, wr₆a, wr₅]
  obtain rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₆b, rd₆a, rd₅]
  obtain sp₆' : s₆.sp = s.sp := by rw [sp₆, sp₆b, sp₆a, sp₅]
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp r2₆ hv) fun s₇ ⟨r3₇, o₇, m₇, rd₇, wr₇, sp₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a, sp₈a⟩ := addImm_ok s₇ .r0 sb (BitVec.ofNat 32 (4 * tailSlot)) (by decide)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈, sp₈⟩ := movR_ok s₈a .r12 .r1
  obtain mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈a, m₇, mem₆]
  obtain g₈ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₈.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [o₈ r h12, o₈a r h0, o₇ r h3 h4]
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [show ([slotAddr .r0 tailSlot, movR .r12 .r1] : List Instr) =
      [.dp .add .r0 sb (.imm (BitVec.ofNat 32 (4 * tailSlot)))] ++ [movR .r12 .r1] from rfl,
      runBlock_app, e₈a, Option.bind_some]; exact e₈, ?_⟩)
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈a, rd₇, rd₆']
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈a, wr₇, wr₆']
  refine WP.mono (copyBlocks_wp (A := T) (B := A) hc0 hc8 hTn hAn
    (fun t ht h4 => by rw [rd₈', wr₈']; exact inRd (inT t ht h4))
    (fun t ht h4 => by rw [wr₈']; exact inA t ht h4) sepAT.symm
    ⟨by rw [o₈ _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₆]; simp [T],
      by rw [r₈, o₈a _ (by decide), o₇ _ (by decide) (by decide), r1₆]; simp [A],
      by rw [o₈ _ (by decide), o₈a _ (by decide), r3₇, Nat.sub_zero], ⟨fun t ht => by omega_arith, Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩) fun s₉ h₉ => ?_
  obtain f₉ : Frame [⟨State.addr A, 16 * c⟩] s₅.mem s₉.mem := by rw [← mem₈]; exact h₉.cp.frame
  obtain g₉ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s₉.gpr r = s₆.gpr r :=
    fun r h0 h12 h3 h4 => by rw [h₉.regs r h0 h12 h3 h4, g₈ r h0 h12 h3 h4]
  obtain sc₉ : ScrOk s₀ b g E s₉.mem := sc₅.frame hg hfit' f₉ koA
  obtain wr₉ : s₉.wr = s.wr := by rw [h₉.wr, wr₈']
  obtain rd₉ : s₉.rd = s.rd := by rw [h₉.rd, rd₈']
  obtain sp₉ : s₉.sp = s.sp := by rw [h₉.sp, sp₈, sp₈a, sp₇, sp₆']
  -- The blocks the eight-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, blk s₄ j =
      Spec.Camellia.blockAt s₀.mem (State.addr D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [blk, Spec.Camellia.blockAt, Vector.getElem_ofFn]
    have := h₃.cp.copied (16 * j + u) (by omega_arith)
    rw [hT, VG.Offset.add_add, hA, VG.Offset.add_add] at this
    obtain hout : ∀ r ∈ [(⟨wordAddr b dSlot, 4⟩ : Region), ⟨wordAddr b nSlot, 4⟩, ⟨wordAddr b endSlot, 4⟩],
        ¬ r.Contains (State.addr b + BitVec.ofNat 64 (4 * tailSlot + (16 * j + u))) 1 := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        rw [slot_addr (by (try simp only [dSlot_eq, nSlot_eq, endSlot_eq]); omega_arith)] <;>
        exact not_contains_off _ (by (try simp only [tailSlot_eq, dSlot_eq, nSlot_eq, endSlot_eq]); omega_arith)
          (by rw [tailSlot_eq]; omega_arith) (by omega_arith) (by (try simp only [dSlot_eq, nSlot_eq, endSlot_eq]); omega_arith)
    rw [base₄, VG.Offset.add_add, show 4 * tailSlot + 16 * j + u = 4 * tailSlot + (16 * j + u) by omega_arith,
      fs _ hout, this, mem₂, hi.data _ (by omega_arith), ite_eq_right (by omega_arith), VG.Offset.add_add,
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith]
  obtain hdata : DInv s₀.mem s₉.mem (State.addr D) n (8 * k + c) (outF s₀.mem (State.addr D) g E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : State.addr D + BitVec.ofNat 64 i = State.addr A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [hA, VG.Offset.add_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, h₉.cp.copied _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : State.addr T + BitVec.ofNat 64 (i - 128 * k) =
          State.addr (s₅.gpr sb) + BitVec.ofNat 64 (4 * tailSlot + 16 * ((i - 128 * k) / 16)) +
            BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [base₅, hT, VG.Offset.add_add, VG.Offset.add_add,
          show 4 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 = 4 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (blk s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨State.addr A, 16 * c⟩ : Region)], ¬ r.Contains (State.addr D + BitVec.ofNat 64 i) 1 :=
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hA]
          exact not_contains_off _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      rw [f₉ _ hout,
        f₅.bytes (R := ⟨State.addr D, 16 * n⟩) (dD (ctx_sub_scr hfit')) (by simp only; omega_arith) hin,
        fs.bytes (R := ⟨State.addr D, 16 * n⟩) (dD hsub) (by simp only; omega_arith) hin,
        f₃.bytes (R := ⟨State.addr D, 16 * n⟩) (dD fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subT) (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  obtain fr₉ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s.mem s₉.mem := by
    refine ((f₃.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((fs.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, hsub r hr⟩).trans
      ((f₅.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ctx_sub_scr hfit' r hr⟩).trans
      (f₉.sub fun r hr => ⟨⟨State.addr D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))))
    · simp only [List.mem_singleton] at hr; subst hr; exact subT
    · simp only [List.mem_singleton] at hr; subst hr; exact subA
  -- On to the next group.
  obtain r2₉ : s₉.gpr .r2 = BitVec.ofNat 32 v := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), r2₆]
  unfold advance
  refine WP.seq (WP.mono (groupCount_wp r2₉ hv) fun s₁₀ ⟨r3₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀, sp₁₀⟩ => ?_)
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁, sp₁₁⟩ := addImm_ok s₁₀ .r1 .r1 128 (by decide)
  obtain ⟨s₁₂, e₁₂, r₁₂, z₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂, sp₁₂⟩ := subsR_ok s₁₁ .r2 .r2 .r3
  refine WP.of_runBlock ⟨s₁₂, by
    rw [show ([.dp .add .r1 .r1 (.imm 128), .subs .r2 .r2 (.reg .r3)] : List Instr) =
      [.dp .add .r1 .r1 (.imm 128)] ++ [.subs .r2 .r2 (.reg .r3)] from rfl,
      runBlock_app, e₁₁, Option.bind_some, e₁₂], ?_⟩
  obtain zz : s₁₂.z = decide (v = c) := by
    rw [z₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
      ofNat32_sub_beq (by omega_arith) (by omega_arith)]
  obtain hmem : s₁₂.mem = s₉.mem := by rw [m₁₂, m₁₁, m₁₀]
  obtain base₁₂ : s₁₂.gpr sb = b := by
    rw [o₁₂ _ (by decide), o₁₁ _ (by decide), o₁₀ _ (by decide) (by decide),
      g₉ _ (by decide) (by decide) (by decide) (by decide), base₆]
  obtain rd₁₂' : s₁₂.rd = s₀.rd := by rw [rd₁₂, rd₁₁, rd₁₀, rd₉, hi.rd]
  obtain wr₁₂' : s₁₂.wr = s₀.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₉, hi.wr]
  obtain sp₁₂' : s₁₂.sp = s₀.sp := by rw [sp₁₂, sp₁₁, sp₁₀, sp₉, hi.sp]
  obtain fr : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₁₂.mem := by
    rw [hmem]; exact hi.frame.trans fr₉
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [zz]; simp; omega_arith, base₁₂, hmem ▸ sc₉, by have := hmem ▸ hdata; rwa [hn] at this, fr,
      rd₁₂', wr₁₂', sp₁₂'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨by rw [zz]; simp; omega_arith, base₁₂, ?_, ?_, by omega_arith, ?_, hmem ▸ sc₉,
      by rw [hmem, show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata, fr, rd₁₂', wr₁₂', sp₁₂'⟩
    · rw [o₁₂ _ (by decide), r₁₁, o₁₀ _ (by decide) (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide),
        r1₆]
      simp only [A]
      rw [show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, VG.Offset.add_add,
        show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [r₁₂, o₁₁ _ (by decide), o₁₁ _ (by decide), r3₁₀, o₁₀ _ (by decide) (by decide), r2₉,
        VG.Offset.ofNat_sub_ofNat (by omega_arith), show v - c = n - 8 * (k + 1) by omega_arith]
    · rw [o₁₂ _ (by decide), o₁₁ _ (by decide), o₁₀ _ (by decide) (by decide),
        g₉ _ (by decide) (by decide) (by decide) (by decide), lr₆]

end VG.Proof.Camellia.Arm

end

end


/-!
# Camellia ECB on ARMv7: the whole function

`ecb_wp`: with the working space as a stack argument (`ecbArm`), `ecb dir`
saves the callee-saved registers, builds the table of subkeys for 18 or 24
rounds in the order `dir` uses them, transforms the blocks a group at a
time (`dataGroup_wp`) and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Camellia.Arm
open VG.Proof.Camellia (DInv outF blocksAt_of_dinv ecb_eq outF_spec schedWords_getD dirPerm dirPerm_lt
  wordAt_frame)
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)

/-- The specification's direction. -/
def specDir : Dir → Spec.Camellia.Direction
  | .encrypt => .encrypt
  | .decrypt => .decrypt

/-- ECB on ARMv7 with its working space at the first stack argument. -/
def ecbArm (dir : Dir) : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 272⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 16 * (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 4 * slots⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      (s.gpr .r0).toNat + 272 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 4 * slots ≤ 2 ^ 32 ∧ ((s.gpr .r1).toNat = 18 ∨ (s.gpr .r1).toNat = 24)
  post s s' :=
    Spec.Camellia.blocksAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Camellia.ecb (Spec.Camellia.subkeysAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (specDir dir)
        (Spec.Camellia.blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- The order of the subkeys in the table, for each direction. -/
def permOf (dir : Dir) : Nat → Nat → Nat := dirPerm (specDir dir)

theorem exec_movR (s : State) (d n : Reg) : exec (movR d n) s = some (s.setReg d (s.gpr n)) := by
  simp [movR, exec, Op2.eval]

/-- The subkeys the loop bitslices, for `g` groups. -/
def cntOf : Dir → Nat → Nat
  | .encrypt, g => 8 * g + 2
  | .decrypt, g => 8 * g - 2

/-- How far `groupConsts` moves `r12`. -/
def r12Of : Dir → Nat → Nat
  | .encrypt, _ => 0
  | .decrypt, g => 64 * g

theorem groupConsts_ok (dir : Dir) {g : Nat} (hg : g = 3 ∨ g = 4) (s : State) :
    ∃ s', runBlock isa (groupConsts dir g) s = some s' ∧ s'.gpr .lr = BitVec.ofNat 32 (cntOf dir g) ∧
      s'.gpr u7 = s.gpr u7 + BitVec.ofNat 32 (r12Of dir g) ∧
      (∀ r, r ≠ .lr → r ≠ u7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp := by
  cases dir
  · refine ⟨s.setReg .lr (BitVec.ofNat 32 (8 * g + 2)), ?_, RegUpd.gpr_setReg_self _ _ _, ?_,
      fun r h1 _ => RegUpd.gpr_setReg_of_ne _ _ h1, rfl, rfl, rfl, rfl⟩
    · rw [groupConsts, runBlock_cons, exec_movImm (by rcases hg with rfl | rfl <;> decide), runStep_some,
        runBlock_nil]
    · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide)]; simp [r12Of]
  · let s₁ := s.setReg .r12 (s.gpr .r12 + BitVec.ofNat 32 (64 * g))
    refine ⟨s₁.setReg .lr (BitVec.ofNat 32 (8 * g - 2)), ?_, RegUpd.gpr_setReg_self _ _ _, ?_,
      fun r h1 h2 => by rw [RegUpd.gpr_setReg_of_ne _ _ h1]; exact RegUpd.gpr_setReg_of_ne _ _ h2, rfl, rfl, rfl,
      rfl⟩
    · rw [groupConsts, runBlock_cons, exec_addImm (by rcases hg with rfl | rfl <;> decide), runStep_some,
        runBlock_cons, exec_movImm (by rcases hg with rfl | rfl <;> decide), runStep_some, runBlock_nil]
    · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), show u7 = Reg.r12 from rfl, RegUpd.gpr_setReg_self]; rfl

/-- `KeysPost` from the state after `groupConsts`, which wrote only `lr` and `r12`. -/
theorem KeysPost.of_consts {s₀ s₁ s : State} {b sched : BitVec 32} {g : Nat} {perm : Nat → Nat}
    (h : KeysPost s₁ b sched g perm s) (hm : s₁.mem = s₀.mem) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (ho : ∀ r, r ≠ .lr → r ≠ u7 → s₁.gpr r = s₀.gpr r) : KeysPost s₀ b sched g perm s :=
  ⟨h.pre, fun i hi => hm ▸ h.ent i hi, hm ▸ h.frame,
    fun r h1 h2 => by
      rw [h.regs r h1 h2, ho r (fun h => h1 (by subst h; decide)) (fun h => h1 (by subst h; decide))],
    h.rd.trans hrd, h.wr.trans hwr, h.kpos⟩

/-- The postwhitening's address, to `lr`. -/
theorem endAddr_ok {s : State} {b : BitVec 32} {g : Nat} (hk : AtEntry s b (8 * g + 2)) :
    ∃ s', runBlock isa endAddr s = some s' ∧ s'.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧
      s'.mem = s.mem ∧ (∀ r, r ≠ .lr → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨s.setReg .lr (s.gpr kp - 128), ?_, ?_, rfl, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩
  · simp only [endAddr, runBlock_cons, exec, Op2.eval, show encodable 128 = true by decide, ↓reduceIte,
      Option.map_some, runStep_some, runBlock_nil]
  · rw [RegUpd.gpr_setReg_self, hk, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, BitVec.sub_eq_add_neg,
      BitVec.add_assoc, ← BitVec.sub_eq_add_neg, VG.Offset.ofNat_sub_ofNat (by rw [keySlot_eq]; omega_arith),
      show 4 * keySlot + 64 * (8 * g + 2) - 128 = 4 * keySlot + 512 * g by rw [keySlot_eq]; omega_arith]

theorem keys_wp (dir : Dir) {s₀ : State} {b sched : BitVec 32} {g : Nat} (hg : g = 3 ∨ g = 4)
    (hz : isa.eval .eq s₀ = some (decide (g = 3))) (hk : KeyPre s₀ b sched) (hr : s₀.gpr u7 = sched) :
    WP isa (keys dir) s₀ fun s => ∃ s₁, KeysPost s₀ b sched g (permOf dir g) s₁ ∧
      s.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧ s.mem = s₁.mem ∧
      (∀ r, r ≠ .lr → s.gpr r = s₁.gpr r) ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₀.sp := by
  unfold keys
  refine WP.seq (WP.mono (M := isa) (Q := fun s₁ => s₁.gpr .lr = BitVec.ofNat 32 (cntOf dir g) ∧
      s₁.gpr u7 = s₀.gpr u7 + BitVec.ofNat 32 (r12Of dir g) ∧
      (∀ r, r ≠ .lr → r ≠ u7 → s₁.gpr r = s₀.gpr r) ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.sp = s₀.sp)
    (WP.ite (decide (g = 3)) hz (fun h => ?_) (fun h => ?_)) fun s₁ h₁ => ?_)
  · obtain rfl : g = 3 := by simpa using h
    obtain ⟨s', e', h'⟩ := groupConsts_ok dir hg s₀
    exact WP.of_runBlock ⟨s', e', h'⟩
  · obtain rfl : g = 4 := by simp at h; omega_arith
    obtain ⟨s', e', h'⟩ := groupConsts_ok dir hg s₀
    exact WP.of_runBlock ⟨s', e', h'⟩
  obtain ⟨l₁, r₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := h₁
  obtain hk₁ : KeyPre s₁ b sched := hk.congr (o₁ _ (by decide) (by decide)) rd₁ wr₁
  obtain post : ∀ s₂, KeysPost s₁ b sched g (permOf dir g) s₂ → s₂.sp = s₁.sp →
      WP isa (.block endAddr) s₂ fun s => ∃ s₂, KeysPost s₀ b sched g (permOf dir g) s₂ ∧
        s.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧ s.mem = s₂.mem ∧
        (∀ r, r ≠ .lr → s.gpr r = s₂.gpr r) ∧ s.rd = s₂.rd ∧ s.wr = s₂.wr ∧ s.sp = s₀.sp := by
    intro s₂ h sp₂
    obtain ⟨s', e', l', m', g', rd', wr', sp'⟩ := endAddr_ok h.kpos
    exact WP.of_runBlock ⟨s', e', s₂, h.of_consts m₁ rd₁ wr₁ o₁, l', m', g', rd', wr', sp'.trans (sp₂.trans sp₁)⟩
  cases dir
  · exact WP.seq (WP.mono (WP.sp (encKeys_wp hg hk₁ (by rw [r₁, hr]; simp [r12Of]) l₁)) fun s h => post s h.1 h.2)
  · exact WP.seq (WP.mono (WP.sp (decKeys_wp hg hk₁ (by rw [r₁, hr]; simp only [r12Of]; congr 2; omega_arith) l₁))
      fun s h => post s h.1 h.2)

theorem dataLoop_wp {s₀ : State} {b D : BitVec 32} {n g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n)
    (hg : g = 3 ∨ g = 4) {s : State} (hi : GInv s₀ b D n g E 0 s) :
    WP isa (.loop Impl.Camellia.Arm.group .ne) s (GDone s₀ b D n g E) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - 8 * k ∧ GInv s₀ b D n g E k s) (fun m s hs => ?_) n s
    ⟨0, by omega_arith, hi⟩
  obtain ⟨k, rfl, hk⟩ := hs
  refine WP.mono (dataGroup_wp hp hg hk) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨(eval_ne s').trans (by rw [z]; rfl), d⟩
  · exact .inr ⟨(eval_ne s').trans (by rw [z]; rfl), n - 8 * (k + 1),
      by have := d.lt; have := hk.lt; omega_arith, k + 1, rfl, d⟩

/-- The prologue: the scratch buffer's address from the stack to `sb`, the
registers saved, the schedule's pointer in `r12`, `rounds` compared with 18,
the data pointer in `r1` and `n` in `r2`. -/
theorem prologue_ok {s₀ : State} {b : BitVec 32} (hb : stackArg s₀ 0 = b) (hw : ScrIn s₀.wr b)
    (ha : (⟨stackArgAddr s₀ 0, 4⟩ : Region) ∈ s₀.rd) :
    ∃ s, runBlock isa (([.ldrSp .r12 0] : List Instr) ++ saveRegs .r12 ++
        ([movR sb .r12, movR .r12 .r0, .cmp .r1 (.imm 18), movR .r1 .r2, movR .r2 .r3] : List Instr)) s₀ = some s ∧
      s.gpr sb = b ∧ s.gpr .r12 = s₀.gpr .r0 ∧ s.gpr .r1 = s₀.gpr .r2 ∧ s.gpr .r2 = s₀.gpr .r3 ∧
      s.z = (s₀.gpr .r1 - 18 == 0) ∧ Saved s₀ b s.mem ∧ Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s.mem ∧
      s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp := by
  obtain hin : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 0)) 4 :=
    ⟨_, List.mem_append_left _ ha, Region.contains_self _ _⟩
  let u := s₀.setReg .r12 b
  obtain e₀ : exec (.ldrSp .r12 0) s₀ = some u := by
    subst hb
    simp only [exec, show (0 : Nat) < 4096 by decide, ↓reduceIte, State.load32, hin, Option.map_some]
    rfl
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, sp₂, f₂, -⟩ := save_ok (s := u) (base := .r12) hw
    (RegUpd.gpr_setReg_self _ _ _)
  let s₃ := s₂.setReg sb (s₂.gpr .r12)
  let s₄ := s₃.setReg .r12 (s₃.gpr .r0)
  let s₅ := subFlags s₄ (s₄.gpr .r1) 18
  let s₆ := s₅.setReg .r1 (s₅.gpr .r2)
  let s₇ := s₆.setReg .r2 (s₆.gpr .r3)
  obtain e₅ : exec (.cmp .r1 (.imm 18)) s₄ = some s₅ := by
    simp only [exec, Op2.eval, show encodable (18 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
    rfl
  obtain hu : ∀ r, r ≠ .r12 → u.gpr r = s₀.gpr r := fun r h => RegUpd.gpr_setReg_of_ne _ _ h
  refine ⟨s₇, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  · rw [runBlock_app, runBlock_app, runBlock_cons, e₀, runStep_some, runBlock_nil, Option.bind_some, e₂,
      Option.bind_some, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR, runStep_some,
      runBlock_cons, e₅, runStep_some, runBlock_cons, exec_movR, runStep_some, runBlock_cons, exec_movR,
      runStep_some, runBlock_nil]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), subFlags_gpr,
      RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self, g₂, RegUpd.gpr_setReg_self]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), subFlags_gpr,
      RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self, subFlags_gpr,
      RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (by decide), subFlags_gpr,
      RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · rw [RegUpd.z_setReg, RegUpd.z_setReg, subFlags_z, RegUpd.gpr_setReg_of_ne _ _ (by decide),
      RegUpd.gpr_setReg_of_ne _ _ (by decide), g₂, hu _ (by decide)]
  · show s₂.mem.readW _ 32 = _
    rw [sv₂ i hi, hu _ (sreg_ne_r12 i hi)]
  · exact f₂
  · exact rd₂
  · exact wr₂
  · exact sp₂

/-! ## The whole function -/

theorem ecb_wp (dir : Dir) {s₀ : State} (hp : (ecbArm dir).pre s₀) :
    WP isa (ecb dir) s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (ecbArm dir).post s₀ s' := by
  obtain ⟨hrd, hwr, dSD, dSS, dDS, -, -, -, fitK, fitD, fitB, hR⟩ := hp
  generalize hb : stackArg s₀ 0 = b at hwr dSS dDS fitB
  let D := s₀.gpr .r2
  let n := (s₀.gpr .r3).toNat
  let sched := s₀.gpr .r0
  let R := (s₀.gpr .r1).toNat
  obtain hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp, fitB⟩
  obtain hwD : (⟨State.addr D, 16 * n⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [D, n]
  obtain hrK : (⟨State.addr sched, 272⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [sched]
  obtain hrA : (⟨stackArgAddr s₀ 0, 4⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have hfitB := fitB
  rw [slots_eq] at hfitB
  unfold ecb
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, r12₁, r1₁, r2₁, z₁, sv₁, f₁, rd₁, wr₁, sp₁⟩ := prologue_ok hb hwS hrA
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  obtain hk₁ : KeyPre s₁ b sched :=
    ⟨b₁, ⟨by rw [wr₁]; exact hwS.mem, fitB⟩, List.mem_append_left _ (by rw [rd₁]; exact hrK), fitK, dSS⟩
  obtain hz₁ : s₁.z = decide (R = 18) := by
    rw [z₁, show s₀.gpr .r1 = BitVec.ofNat 32 R by simp [R],
      show (18 : BitVec 32) = BitVec.ofNat 32 18 from rfl, ofNat32_sub_beq (by omega_arith) (by decide)]
  -- The table.
  obtain ⟨g, hgR⟩ : ∃ g, R / 6 = g := ⟨_, rfl⟩
  obtain hg : g = 3 ∨ g = 4 := by omega_arith
  let KQ : State → Prop := fun s => ∃ s', KeysPost s₁ b sched g (permOf dir g) s' ∧
      s.gpr .lr = b + BitVec.ofNat 32 (4 * keySlot + 512 * g) ∧ s.mem = s'.mem ∧
      (∀ r, r ≠ .lr → s.gpr r = s'.gpr r) ∧ s.rd = s'.rd ∧ s.wr = s'.wr ∧ s.sp = s₁.sp
  refine WP.seq (WP.mono (M := isa) (Q := KQ) (keys_wp dir hg ((eval_eq s₁).trans (by
      rw [hz₁]; exact congrArg some (decide_eq_decide.mpr ⟨fun h => by omega_arith, fun h => by omega_arith⟩))) hk₁ r12₁)
    fun s₂ ⟨s₂', k₂, lr₂, m₂, g₂, rd₂', wr₂', sp₂⟩ => ?_)
  -- The scratch buffer and the data before the groups.
  let E : Nat → BitVec 64 := fun i => (schedWords s₀.mem (State.addr sched) R).getD (permOf dir g i) 0
  obtain f₀₂ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₂.mem := by
    rw [m₂]
    exact f₁.trans (k₂.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact table_sub_scr fitB⟩)
  obtain base₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide)]; exact k₂.pre.base
  obtain hE : ∀ i < 8 * g + 2,
      Spec.Camellia.wordAt s₁.mem (State.addr sched + BitVec.ofNat 64 (8 * permOf dir g i)) = E i :=
    fun i hi => by
      obtain hp : permOf dir g i < 8 * g + 2 := dirPerm_lt (specDir dir) hi
      rw [show E i = _ from schedWords_getD s₀.mem (State.addr sched) (R := R)
        (by simp only [Spec.Camellia.scheduleLength]; omega_arith)]
      exact hk₁.wordAt_eq f₁ (by omega_arith)
  obtain sc₂ : ScrOk s₀ b g E s₂.mem := by
    refine ⟨fun i hi => by rw [m₂]; exact hE i hi ▸ k₂.ent i hi, fun i hi => ?_⟩
    rw [← sv₁ i hi, m₂]
    refine slot_keep fitB (lo := savedSlot) (hi := slots) (Nat.le_refl _) k₂.frame (fun r hr => ?_)
      (Nat.le_add_right _ _) (by rw [savedSlot_eq, slots_eq]; omega_arith)
    simp only [List.mem_singleton] at hr; subst hr
    simp only [tableRegion]
    rw [VG.Arm.addr_add (by rw [keySlot_eq]; omega_arith)]
    exact VG.Offset.disjoint _ (by rw [savedSlot_eq, keySlot_eq]; omega_arith) (by rw [savedSlot_eq, slots_eq]; omega_arith)
      (by rw [keySlot_eq]; omega_arith)
  obtain data₂ : ∀ i < 16 * n, s₂.mem (State.addr D + BitVec.ofNat 64 i) = s₀.mem (State.addr D + BitVec.ofNat 64 i) :=
    fun i hi => f₀₂.bytes (R := ⟨State.addr D, 16 * n⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dDS) (by simp only; omega_arith) hi
  obtain fr₂ : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr D, 16 * n⟩] s₀.mem s₂.mem :=
    f₀₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  obtain rd₂ : s₂.rd = s₀.rd := by rw [rd₂', k₂.rd, rd₁]
  obtain wr₂ : s₂.wr = s₀.wr := by rw [wr₂', k₂.wr, wr₁]
  obtain sp₂' : s₂.sp = s₀.sp := by rw [sp₂, sp₁]
  obtain r1₂ : s₂.gpr .r1 = D := by
    rw [g₂ _ (by decide), k₂.regs _ (by decide) (by decide), r1₁]
  obtain r2₂ : s₂.gpr .r2 = BitVec.ofNat 32 n := by
    rw [g₂ _ (by decide), k₂.regs _ (by decide) (by decide), r2₁]; simp [n]
  -- Any blocks?
  let s₄ := subFlags s₂ (s₂.gpr .r2) 0
  obtain e₄ : runBlock isa [.cmp .r2 (.imm 0)] s₂ = some s₄ := by
    rw [runBlock_cons, show exec (.cmp .r2 (.imm 0)) s₂ = some s₄ by
      simp only [exec, Op2.eval, show encodable (0 : BitVec 32) = true by decide, ↓reduceIte, Option.map_some]
      rfl,
      runStep_some, runBlock_nil]
  obtain hz₄ : s₄.z = decide (n = 0) := by
    show (s₂.gpr .r2 - 0 == 0) = _
    rw [r2₂, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    have : n < 2 ^ 32 := (s₀.gpr .r3).isLt
    bv_omega
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have base₄ : s₄.gpr sb = b := base₂
  have mem₄ : s₄.mem = s₂.mem := rfl
  have rd₄ : s₄.rd = s₀.rd := rd₂
  have wr₄ : s₄.wr = s₀.wr := wr₂
  have sp₄ : s₄.sp = s₀.sp := sp₂'
  refine WP.seq (WP.mono (M := isa) (Q := GDone s₀ b D n g E)
    (WP.ite (decide (n = 0)) ((eval_eq s₄).trans (by rw [hz₄])) (fun h0 => ?_) (fun h0 => ?_))
    fun s₅ d₅ => ?_)
  · have hn0 : n = 0 := by simpa using h0
    exact WP.block_nil ⟨base₄, mem₄ ▸ sc₂, fun i hi => by omega_arith, mem₄ ▸ fr₂, rd₄, wr₄, sp₄⟩
  · have hn0 : n ≠ 0 := by simpa using h0
    refine dataLoop_wp ⟨hwS, hwD, dDS, fitD⟩ hg ⟨base₄, by show s₂.gpr .r1 = _; rw [r1₂]; simp,
      by show s₂.gpr .r2 = _; rw [r2₂, Nat.mul_zero, Nat.sub_zero], by omega_arith, lr₂,
      mem₄ ▸ sc₂, fun i hi => ?_, mem₄ ▸ fr₂, rd₄, wr₄, sp₄⟩
    rw [mem₄, data₂ i hi, ite_eq_right (by omega_arith)]
  -- The epilogue.
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := movR_ok s₅ .r12 sb
  obtain ⟨s₇, e₇, rg₇, -, m₇, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [wr₆, d₅.wr]; exact hwS)
    (by rw [r₆, d₅.base]) (by rw [m₆]; exact d₅.scr.saved)
  refine WP.of_runBlock ⟨s₇, by rw [runBlock_app, e₆, Option.bind_some, e₇], rg₇, ?_⟩
  obtain hd₇ : DInv s₀.mem s₇.mem (State.addr D) n n (outF s₀.mem (State.addr D) g E) := fun i hi => by
    rw [m₇, m₆]; exact d₅.data i hi
  show Spec.Camellia.blocksAt s₇.mem (State.addr D) n = _
  rw [blocksAt_of_dinv hd₇, ecb_eq]
  simp only [Spec.Camellia.blocksAt, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  subst hgR
  exact outF_spec (specDir dir) s₀.mem (State.addr sched) (State.addr D) hR j

end VG.Proof.Camellia.Arm
