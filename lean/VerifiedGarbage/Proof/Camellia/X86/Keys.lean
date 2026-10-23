module
public import VerifiedGarbage.Proof.Camellia.X86.Core

import VerifiedGarbage.Proof.Camellia.X86.Prologue
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.X86.Copy
import VerifiedGarbage.Proof.Camellia.X86.Crypt8
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The table of bitsliced subkeys on x86 (32-bit)

As on ARMv7 (`Proof/Camellia/Arm/Keys.lean`): `encKeys g` and `decKeys g`
bitslice the subkeys of the schedule at `ecx` into the table at slot 104,
entry `i` holding the subkey word `perm i`: `keyOne_step` is one subkey,
each of its two 32-bit words loaded to slot 0 and turned into its eight
planes (`keyPlane`, checked by evaluation), and `keyLoop_wp` the loop of
them, counted down in `ebp`.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Bitslice (lanes bitOf xorBits bitOf_word xorBits_cons xorBits_nil)
open VG.Impl.Aes.X86 (sb tmpRegs slotAt st movR addI subI movI at_ argOp)
open VG.Proof.Camellia (byteOf_wordAt)

/-- The table's entry `e` holds `k` for every block. -/
abbrev EntryOk (m : Mem) (b : BitVec 32) (e : Nat) (k : BitVec 64) : Prop :=
  W32.HalfRel (entryW m b e) fun _ => k

/-- The scratch buffer at `b` and the schedule's 34 words at `sched`, apart. -/
structure KeyPre (s : State) (b sched : BitVec 32) : Prop where
  base : s.gpr sb = b
  scr : ScrIn s.wr b
  sch : (⟨sched.setWidth 64, 272⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 272 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨sched.setWidth 64, 272⟩ ⟨b.setWidth 64, 4 * slots⟩

theorem KeyPre.congr {s s' : State} {b sched : BitVec 32} (h : KeyPre s b sched) (hb : s'.gpr sb = s.gpr sb)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : KeyPre s' b sched :=
  ⟨hb.trans h.base, hwr ▸ h.scr, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

/-- Byte `v` of subkey `w` of the schedule. -/
theorem sched_addr {sched : BitVec 32} (hfit : sched.toNat + 272 ≤ 2 ^ 32) {w v : Nat} (hw : 8 * w + v < 272) :
    addr (sched + BitVec.ofNat 32 (8 * w)) v = sched.setWidth 64 + BitVec.ofNat 64 (8 * w + v) := by
  rw [addr, VG.Offset.add_add, ← addr, addr_eq (by omega_arith)]

theorem KeyPre.word_in {s : State} {b sched : BitVec 32} (h : KeyPre s b sched) {w v : Nat}
    (hw : 8 * w + v + 4 ≤ 272) :
    InRegions (s.rd ++ s.wr) (addr (sched + BitVec.ofNat 32 (8 * w)) v) 4 := by
  refine ⟨_, h.sch, ?_⟩
  have := setWidth_toNat sched
  rw [sched_addr h.schFit (by omega_arith)]
  exact VG.Offset.contains_base _ (by have := h.schFit; omega_arith) (by omega_arith)

/-- The schedule is outside the scratch buffer. -/
theorem KeyPre.wordAt_eq {s : State} {b sched : BitVec 32} (h : KeyPre s b sched) {m m' : Mem}
    (hf : Frame [⟨b.setWidth 64, 4 * slots⟩] m m') {w : Nat} (hw : w < 34) :
    Spec.Camellia.wordAt m' (sched.setWidth 64 + BitVec.ofNat 64 (8 * w)) =
      Spec.Camellia.wordAt m (sched.setWidth 64 + BitVec.ofNat 64 (8 * w)) := by
  refine VG.Proof.Camellia.wordAt_frame hf fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact h.sep.sub_left (VG.Offset.sub_base _ (by omega_arith))

/-- The entry `e` of the table. -/
def entryRegion (b : BitVec 32) (e : Nat) : Region :=
  ⟨(b + BitVec.ofNat 32 (4 * keySlot + 64 * e)).setWidth 64, 64⟩

/-- The entry at `kp`, for the planes' stores; slot 0, for the word. -/
theorem ok_entry {s : State} {b : BitVec 32} {e : Nat} (hs : ScrIn s.wr b) (hb : s.gpr sb = b)
    (hk : AtEntry s b e) (he : e < 34) : Ok entryCfg s where
  slotIn k hk' := by
    simp only [entryCfg] at hk' ⊢
    rw [wordAddr_entry hk]; exact hs.slot (by rw [slots_eq, keySlot_eq]; omega_arith)
  extIn j hj := by
    simp only [entryCfg] at hj ⊢
    rw [hb]; exact hs.slot_rd (by rw [slots_eq]; omega_arith)
  fit := by
    have := hs.fit
    simp only [entryCfg]
    rw [show s.gpr kp = _ from hk, BitVec.toNat_add, BitVec.toNat_ofNat, keySlot_eq]
    rw [slots_eq] at this
    rw [Nat.mod_eq_of_lt (a := 4 * 104 + 64 * e) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  sep k hk' j hj := by
    have := hs.fit
    simp only [entryCfg] at hk' hj ⊢
    rw [wordAddr_entry hk, hb]
    rw [slots_eq] at this
    exact slot_sep b (by rw [keySlot_eq]; omega_arith) (by omega_arith) (by rw [keySlot_eq]; omega_arith)

theorem keyPlanes_all (w : Nat) (hw : w = 0 ∨ w = 1) :
    ([Reg.esp, .esi, .edi, .ecx, .ebp, .eax].all fun r =>
      ((List.range 8).flatMap (keyPlane w)).all fun i => i.dst != some r) = true := by
  rcases hw with rfl | rfl <;> decide +kernel

/-- The planes of the word in slot 0 to words `8 w …` of the entry `e` at `kp`. -/
theorem keyPlanes_step {s : State} {b : BitVec 32} {e w : Nat} (hs : ScrIn s.wr b) (hb : s.gpr sb = b)
    (hk : AtEntry s b e) (he : e < 34) (hw : w = 0 ∨ w = 1) :
    ∃ s', runBlock isa ((List.range 8).flatMap (keyPlane w)) s = some s' ∧
      (∀ j < 8, ∀ p < 32, (entryW s'.mem b e (8 * w + j)).getLsbD p = (slotW s 0).getLsbD (8 * (p / 8) + j)) ∧
      (∀ j < 16, j < 8 * w ∨ 8 * w + 8 ≤ j → entryW s'.mem b e j = entryW s.mem b e j) ∧
      (∀ r, r ∈ [Reg.esp, .esi, .edi, .ecx, .ebp, .eax] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [entryRegion b e] s.mem s'.mem := by
  have hchk : check (lanes 32 9) entryCfg (linExt 0) ((List.range 8).flatMap (keyPlane w)) (linEnv (keyIns w))
      (linPost 16 9 (keyOuts w)) = true := by
    rcases hw with rfl | rfl
    · exact keyPlanes0_check
    · exact keyPlanes1_check
  let W : Nat → BitVec 32 := fun i =>
    if i = 0 then slotW s 0 else s.mem.readW (wordAddr (s.gpr kp) (8 * (1 - w) + (i - 1))) 32
  obtain ⟨s', h', so', rd', wr', o', f'⟩ := linear_ok hchk (ok_entry hs hb hk he) W
    (fun j i hji hj => by
      simp only [keyIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk', rfl, rfl⟩ := hji
      exact ⟨by omega_arith, by simp [W]; rfl⟩)
    (fun j hj => by
      simp only [entryCfg] at hj
      obtain rfl : j = 0 := by omega_arith
      exact ⟨by decide, by simp [W]; rfl⟩)
  have hkeep : ∀ r, r ∈ [Reg.esp, .esi, .edi, .ecx, .ebp, .eax] → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp (keyPlanes_all w hw) r hr)
  refine ⟨s', h', fun j hj p hp => ?_, fun j hj hjw => ?_, hkeep, rd', wr', ?_⟩
  · have := so' (8 * w + j) (keyBsG j)
      (List.mem_append_left _ (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)) p hp
    simp only [entryCfg] at this
    rw [entryW, ← wordAddr_entry hk, this, keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false]
    simp only [bitOf]
    rw [Nat.div_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    rfl
  · have hj' : 8 * (1 - w) + (j - 8 * (1 - w)) = j := by rcases hw with rfl | rfl <;> omega_arith
    have := so' _ _ (List.mem_append_right _ (List.mem_map.mpr
      ⟨j - 8 * (1 - w), List.mem_range.mpr (by rcases hw with rfl | rfl <;> omega_arith), rfl⟩))
    simp only [entryCfg, hj'] at this
    rw [entryW, entryW, ← wordAddr_entry hk]
    refine keep_word (W := W) (i := 1 + (j - 8 * (1 - w))) ?_ this
    simp only [W, show ¬ 1 + (j - 8 * (1 - w)) = 0 by omega_arith, ↓reduceIte,
      show 1 + (j - 8 * (1 - w)) - 1 = j - 8 * (1 - w) by omega_arith, hj']
  · refine f'.mono fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, entryCfg, List.mem_singleton, entryRegion]
    rw [show s.gpr kp = _ from hk]

/-- `mov eax, [ecx + v]; mov [edi], eax`. -/
theorem keyWord_ok (s : State) {b : BitVec 32} (hb : s.gpr sb = b) (hw : ScrIn s.wr b) {v : Nat}
    (h : InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) v) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ .ecx v)), st 0 .eax] s = some s' ∧
      s'.mem = s.mem.writeW (wordAddr b 0) (s.mem.readW (addr (s.gpr .ecx) v) 32) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.setReg .eax (s.mem.readW (addr (s.gpr .ecx) v) 32)
  have e₁ : exec (.mov .eax (.mem (at_ .ecx v))) s = some s₁ := by
    show (s.load32 (addr (s.gpr .ecx) v)).map (s.setReg .eax) = _
    simp only [State.load32, h, ↓reduceIte, Option.map_some]
    rfl
  have b₁ : s₁.gpr sb = b := by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), hb]
  have hin : InRegions s₁.wr (wordAddr (s₁.gpr sb) 0) 4 := by rw [b₁]; exact hw.slot (by decide)
  have e₂ : exec (st 0 .eax) s₁ = some { s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) 0) (s₁.gpr .eax) } := by
    show s₁.store32 (wordAddr (s₁.gpr sb) 0) (s₁.gpr .eax) = _
    simp only [State.store32, hin, ↓reduceIte]
  refine ⟨{ s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) 0) (s₁.gpr .eax) }, ?_, ?_,
    fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil]
  · show s₁.mem.writeW (wordAddr (s₁.gpr sb) 0) (s₁.gpr .eax) = _
    rw [b₁, RegUpd.gpr_setReg_self]; rfl

/-- Regions of the scratch buffer keep the schedule. -/
theorem KeyPre.sched_keep {s : State} {b sched : BitVec 32} (h : KeyPre s b sched) {rs : List Region}
    {m m' : Mem} (hf : Frame rs m m') (hsub : ∀ r ∈ rs, Region.Sub r ⟨b.setWidth 64, 4 * slots⟩) {i : Nat}
    (hi : i < 272) : m' (sched.setWidth 64 + BitVec.ofNat 64 i) = m (sched.setWidth 64 + BitVec.ofNat 64 i) :=
  hf.bytes (R := ⟨sched.setWidth 64, 272⟩) (fun r hr => h.sep.sub_right (hsub r hr)) (by simp only; omega_arith) hi

theorem entry_setWidth {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e : Nat} (he : e < 34) :
    (b + BitVec.ofNat 32 (4 * keySlot + 64 * e)).setWidth 64 =
      b.setWidth 64 + BitVec.ofNat 64 (4 * keySlot + 64 * e) := by
  rw [slots_eq] at hfit; exact addr_eq (by rw [keySlot_eq]; omega_arith)

/-- Slot 0 and the table's entries. -/
def tableRegion (b : BitVec 32) : Region := ⟨b.setWidth 64, 4 * savedSlot⟩

theorem entry_sub_table {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e : Nat} (he : e < 34) :
    Region.Sub (entryRegion b e) (tableRegion b) := by
  simp only [entryRegion, tableRegion]
  rw [entry_setWidth hfit he]
  exact VG.Offset.sub_base _ (by rw [keySlot_eq, savedSlot_eq]; omega_arith)

theorem slot0_sub_table {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    Region.Sub ⟨wordAddr b 0, 4⟩ (tableRegion b) := by
  rw [slots_eq] at hfit
  simp only [tableRegion]
  rw [slot_addr (by omega_arith)]
  exact VG.Offset.sub_base _ (by rw [savedSlot_eq]; omega_arith)

theorem table_sub_scr {b : BitVec 32} :
    Region.Sub (tableRegion b) ⟨b.setWidth 64, 4 * slots⟩ :=
  Region.sub_prefix (by rw [savedSlot_eq, slots_eq]; omega_arith)

theorem keyRegions_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e : Nat} (he : e < 34) :
    ∀ r ∈ [(⟨wordAddr b 0, 4⟩ : Region), entryRegion b e], Region.Sub r (tableRegion b) := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact slot0_sub_table hfit
  · exact entry_sub_table hfit he

theorem sub_trans {r s t : Region} (h₁ : Region.Sub r s) (h₂ : Region.Sub s t) : Region.Sub r t :=
  fun x hx => h₂ x (h₁ x hx)

/-- An entry outside the frame of slot 0 and another entry keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {e i : Nat}
    (hf : Frame [⟨wordAddr b 0, 4⟩, entryRegion b e] m m') (hi : i < 34) (he : e < 34) (hie : i ≠ e) {j : Nat}
    (hj : j < 16) : entryW m' b i j = entryW m b i j := by
  rw [slots_eq] at hfit
  simp only [entryW]
  rw [slot_addr (by rw [keySlot_eq]; omega_arith)]
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [slot_addr (by omega_arith)]
    exact VG.Offset.disjoint _ (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith) (by omega_arith)
  · simp only [entryRegion]
    rw [entry_setWidth (by rw [slots_eq]; omega_arith) he]
    exact VG.Offset.disjoint _ (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)

/-- One 32-bit word of a subkey, at `[ecx + v]`, to words `8 w …` of entry `e`. -/
theorem keyHalf_step {s : State} {b sched : BitVec 32} {e wk v w : Nat} (hk : KeyPre s b sched)
    (hr : s.gpr .ecx = sched + BitVec.ofNat 32 (8 * wk)) (hpos : 8 * wk + v + 4 ≤ 272)
    (hkp : AtEntry s b e) (he : e < 34) (hw : w = 0 ∨ w = 1) :
    ∃ s', runBlock isa (([.mov .eax (.mem (at_ .ecx v)), st 0 .eax] : List Instr) ++ (List.range 8).flatMap (keyPlane w)) s =
        some s' ∧
      (∀ j < 8, ∀ p < 32, (entryW s'.mem b e (8 * w + j)).getLsbD p =
        (s.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * wk + v + p / 8))).getLsbD j) ∧
      (∀ j < 16, j < 8 * w ∨ 8 * w + 8 ≤ j → entryW s'.mem b e j = entryW s.mem b e j) ∧
      (∀ r, r ∈ [Reg.esp, .esi, .edi, .ecx, .ebp] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨wordAddr b 0, 4⟩, entryRegion b e] s.mem s'.mem := by
  have hfit := hk.scr.fit
  have hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .ecx) v) 4 := by rw [hr]; exact hk.word_in hpos
  obtain ⟨s₁, e₁, m₁, o₁, rd₁, wr₁⟩ := keyWord_ok s hk.base hk.scr hin
  have b₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hk.base]
  obtain ⟨s₂, e₂, p₂, k₂, g₂, rd₂, wr₂, f₂⟩ := keyPlanes_step (w := w) (e := e) (by rw [wr₁]; exact hk.scr) b₁
    (by rw [AtEntry, o₁ _ (by decide)]; exact hkp) he hw
  have hs₁0 : slotW s₁ 0 = s.mem.readW (addr (s.gpr .ecx) v) 32 := by
    rw [slotW, b₁, m₁, Mem.readW_writeW_self32]
  have hent₁ : ∀ j < 16, entryW s₁.mem b e j = entryW s.mem b e j := fun j hj => by
    rw [slots_eq] at hfit
    simp only [entryW]
    rw [m₁, Mem.readW_writeW_sep (slot_sep b (by rw [keySlot_eq]; omega_arith) (by omega_arith) (by rw [keySlot_eq]; omega_arith))
      (by decide)]
  refine ⟨s₂, ?_, fun j hj p hp => ?_, fun j hj hjw => ?_, fun r hr => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_⟩
  · rw [runBlock_app, e₁, Option.bind_some, e₂]
  · rw [p₂ j hj p hp, hs₁0, W32.readW32_bit _ _ (by omega_arith) hj, hr, sched_addr hk.schFit (by omega_arith),
      VG.Offset.add_add]
  · rw [k₂ j hj hjw, hent₁ j hj]
  · have hr' : r = .esp ∨ r = .esi ∨ r = .edi ∨ r = .ecx ∨ r = .ebp := by simpa using hr
    rw [g₂ r (by rcases hr' with h | h | h | h | h <;> subst h <;> decide),
      o₁ r (by rcases hr' with h | h | h | h | h <;> subst h <;> decide)]
  · have f₁ : Frame [⟨wordAddr b 0, 4⟩] s.mem s₁.mem := by
      rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    exact (f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; simp [hr], fun _ h => h⟩).trans
      (f₂.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; simp [hr], fun _ h => h⟩)

theorem keyOne_eq (d : Nat) : keyOne d =
    (([.mov .eax (.mem (at_ .ecx (d + 4 * 0))), st 0 .eax] : List Instr) ++ (List.range 8).flatMap (keyPlane 0)) ++
    ((([.mov .eax (.mem (at_ .ecx (d + 4 * 1))), st 0 .eax] : List Instr) ++ (List.range 8).flatMap (keyPlane 1)) ++
      ([addI kp 64] : List Instr)) := by
  simp only [keyOne, List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc, List.cons_append]

/-- One subkey: the two words of schedule word `wk + d / 8`, at `[ecx + d]`, to entry `e`. -/
theorem keyOne_step {s : State} {b sched : BitVec 32} {d e wk : Nat} (hd : d = 0 ∨ d = 8)
    (hk : KeyPre s b sched) (hr : s.gpr .ecx = sched + BitVec.ofNat 32 (8 * wk)) (hw : wk + d / 8 < 34)
    (hkp : AtEntry s b e) (he : e < 34) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧ AtEntry s' b (e + 1) ∧
      (∀ r, r ∈ [Reg.esp, .esi, .edi, .ecx, .ebp] → r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨wordAddr b 0, 4⟩, entryRegion b e] s.mem s'.mem ∧
      EntryOk s'.mem b e
        (Spec.Camellia.wordAt s.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * (wk + d / 8)))) := by
  have hfit := hk.scr.fit
  have hpos : 8 * wk + d + 8 ≤ 272 := by rcases hd with rfl | rfl <;> omega_arith
  obtain ⟨s₁, e₁, p₁, k₁, g₁, rd₁, wr₁, f₁⟩ := keyHalf_step (w := 0) (v := d + 4 * 0) hk hr (by omega_arith) hkp he
    (.inl rfl)
  have hk₁ : KeyPre s₁ b sched := hk.congr (g₁ _ (by decide)) rd₁ wr₁
  obtain ⟨s₂, e₂, p₂, k₂, g₂, rd₂, wr₂, f₂⟩ := keyHalf_step (w := 1) (v := d + 4 * 1) hk₁
    (by rw [g₁ _ (by decide), hr]) (by omega_arith) (by rw [AtEntry, g₁ _ (by decide)]; exact hkp) he (.inr rfl)
  obtain ⟨s₃, e₃, kp₃, -, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ kp 64
  have hsub := keyRegions_sub hfit he
  have hsch₁ : ∀ i < 272, s₁.mem (sched.setWidth 64 + BitVec.ofNat 64 i) = s.mem (sched.setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => hk.sched_keep f₁ (fun r hr => sub_trans (hsub r hr) table_sub_scr) hi
  have hent : ∀ c < 8, ∀ j < 8, ∀ p < 32, p / 8 = c % 4 → (entryW s₂.mem b e (8 * (c / 4) + j)).getLsbD p =
      (s.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * (wk + d / 8) + c))).getLsbD j := by
    intro c hc j hj p hp hpc
    rcases (show c / 4 = 0 ∨ c / 4 = 1 by omega_arith) with h | h
    · rw [h, k₂ _ (by omega_arith) (.inl (by omega_arith))]
      have := p₁ j hj p hp
      rw [Nat.mul_zero, Nat.zero_add] at this
      rw [Nat.mul_zero, Nat.zero_add, this,
        show 8 * wk + (d + 4 * 0) + p / 8 = 8 * (wk + d / 8) + c by rcases hd with rfl | rfl <;> omega_arith]
    · rw [h, p₂ j hj p hp, hsch₁ _ (by omega_arith),
        show 8 * wk + (d + 4 * 1) + p / 8 = 8 * (wk + d / 8) + c by rcases hd with rfl | rfl <;> omega_arith]
  refine ⟨s₃, ?_, hkp.add (n := 1) (by rw [kp₃, g₂ _ (by decide), g₁ _ (by decide)]; rfl), fun r hr hne => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], ?_, ?_⟩
  · rw [keyOne_eq, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · rw [o₃ r hne, g₂ r hr, g₁ r hr]
  · rw [m₃]; exact f₁.trans f₂
  · intro b' hb c hc j hj
    show (entryW s₃.mem b e _).getLsbD _ = _
    rw [m₃, hent c hc j hj _ (by omega_arith) (by omega_arith), byteOf_wordAt _ _ hc, VG.Offset.add_add]

/-! ## The loops -/

/-- The registers the table's construction keeps. -/
theorem keep_regs {r : Reg} (h1 : r ∉ tmpRegs) : r ∈ [Reg.esp, .esi, .edi, .ecx, .ebp] := by
  revert h1; cases r <;> decide

/-- What the loops keep, after `k` of their `N` iterations: the subkeys `F`
in the entries before `e₀ + k`, `ecx` at word `wk k` of the schedule. -/
structure KeyInv (s₀ : State) (b sched : BitVec 32) (e₀ N : Nat) (wk : Nat → Nat) (F : Nat → BitVec 64)
    (k : Nat) (s : State) : Prop where
  pre : KeyPre s b sched
  kpos : AtEntry s b (e₀ + k)
  ptr : s.gpr .ecx = sched + BitVec.ofNat 32 (8 * wk k)
  cnt : s.gpr .ebp = BitVec.ofNat 32 (N - k)
  ent : ∀ i < e₀ + k, EntryOk s.mem b i (F i)
  frame : Frame [tableRegion b] s₀.mem s.mem
  regs : ∀ r, r ∉ tmpRegs → r ≠ kp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loop of `keyOne 0` and `i₁` (`f` on `ecx`), counted down in `ebp`. -/
theorem keyLoop_wp {s₀ s : State} {b sched : BitVec 32} {e₀ N : Nat} {wk : Nat → Nat} {F : Nat → BitVec 64}
    {i₁ : Instr} {f : BitVec 32 → BitVec 32}
    (hop : ∀ s : State, ∃ s', runBlock isa [i₁] s = some s' ∧
      s'.gpr .ecx = f (s.gpr .ecx) ∧ (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (hN : e₀ + N ≤ 34) (hN0 : N < 2 ^ 32)
    (hwk : ∀ k < N, wk k < 34)
    (hstep : ∀ k < N, f (sched + BitVec.ofNat 32 (8 * wk k)) = sched + BitVec.ofNat 32 (8 * wk (k + 1)))
    (hF : ∀ k < N, F (e₀ + k) = Spec.Camellia.wordAt s₀.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * wk k)))
    {k : Nat} (hk : k < N) (hs : KeyInv s₀ b sched e₀ N wk F k s) :
    WP isa (.loop (.block (keyOne 0 ++ ([i₁, subI .ebp 1] : List Instr))) .ne) s
      (KeyInv s₀ b sched e₀ N wk F N) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = N - k ∧ k < N ∧ KeyInv s₀ b sched e₀ N wk F k s)
    (fun n s hs => ?_) (N - k) s ⟨k, rfl, hk, hs⟩
  obtain ⟨k, rfl, hk, hi⟩ := hs
  have hfit := hi.pre.scr.fit
  have hw := hwk k hk
  obtain ⟨s₁, e₁, kp₁, o₁, rd₁, wr₁, f₁, E₁⟩ := keyOne_step (d := 0) (e := e₀ + k) (Or.inl rfl)
    hi.pre hi.ptr (by omega_arith) hi.kpos (by omega_arith)
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := hop s₁
  obtain ⟨s₃, e₃, c₃, z₃, o₃, m₃, rd₃, wr₃⟩ := subI_ok s₂ .ebp 1
  refine WP.of_runBlock ⟨s₃, by
    rw [runBlock_app, e₁, Option.bind_some,
      show ([i₁, subI .ebp 1] : List Instr) = [i₁] ++ [subI .ebp 1] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃], ?_⟩
  have ht₂ : s₂.gpr .ebp = BitVec.ofNat 32 (N - k) := by
    rw [o₂ _ (by decide), o₁ _ (by decide) (by decide), hi.cnt]
  have hc₃ : s₃.gpr .ebp = BitVec.ofNat 32 (N - (k + 1)) := by
    rw [c₃, ht₂, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show N - k - 1 = N - (k + 1) by omega_arith]
  have hm₃ : s₃.mem = s₁.mem := by rw [m₃, m₂]
  have hinv : KeyInv s₀ b sched e₀ N wk F (k + 1) s₃ := by
    refine ⟨hi.pre.congr ?_ ?_ ?_, ?_, ?_, hc₃, fun i hi' => ?_, ?_, fun r h1 h2 => ?_,
      by rw [rd₃, rd₂, rd₁, hi.rd], by rw [wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide) (by decide)]
    · rw [rd₃, rd₂, rd₁]
    · rw [wr₃, wr₂, wr₁]
    · have : AtEntry s₃ b (e₀ + k + 1) := by rw [AtEntry, o₃ _ (by decide), o₂ _ (by decide)]; exact kp₁
      simpa only [Nat.add_assoc] using this
    · rw [o₃ _ (by decide), r₂, o₁ _ (by decide) (by decide), hi.ptr, hstep k hk]
    · by_cases he : i = e₀ + k
      · subst he
        have hw' : Spec.Camellia.wordAt s.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * (wk k + 0 / 8))) =
            F (e₀ + k) := by
          rw [hF k hk, Nat.zero_div, Nat.add_zero]
          exact (hi.pre.wordAt_eq (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
            simp only [List.mem_singleton] at hr; subst hr; exact table_sub_scr⟩) hw)
        rw [← hw', hm₃]
        exact E₁
      · refine (hi.ent i (by omega_arith)).congr fun j hj => ?_
        rw [hm₃]
        exact entryW_frame hfit f₁ (by omega_arith) (by omega_arith) he hj
    · rw [hm₃]
      exact hi.frame.trans (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, keyRegions_sub hfit (by omega_arith) r hr⟩)
    · rw [o₃ r (fun h => h1 (by rw [h]; decide)), o₂ r (fun h => h1 (by rw [h]; decide)),
        o₁ r (keep_regs h1) h2, hi.regs r h1 h2]
  have hz : s₃.zf = some (decide (N - (k + 1) = 0)) := by
    rw [z₃, ← c₃, hc₃, ofNat32_beq_zero (by omega_arith)]
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
    EntryOk s.mem b i (Spec.Camellia.wordAt s₀.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * perm i)))
  frame : Frame [tableRegion b] s₀.mem s.mem
  regs : ∀ r, r ∉ tmpRegs → r ≠ kp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem add8 (x : BitVec 32) {w : Nat} :
    x + BitVec.ofNat 32 (8 * w) + 8 = x + BitVec.ofNat 32 (8 * (w + 1)) := by
  rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, VG.Offset.add_add, show 8 * w + 8 = 8 * (w + 1) by omega_arith]

theorem sub8 (x : BitVec 32) {w : Nat} :
    x + BitVec.ofNat 32 (8 * (w + 1)) - 8 = x + BitVec.ofNat 32 (8 * w) := by
  rw [show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, BitVec.sub_eq_add_neg, BitVec.add_assoc,
    ← BitVec.sub_eq_add_neg, VG.Offset.ofNat_sub_ofNat (by omega_arith), show 8 * (w + 1) - 8 = 8 * w by omega_arith]

/-- `mov ecx, [esp + 4]` and `kp :=` the table. -/
theorem keysSetup_ok {s₀ : State} {b sched : BitVec 32} (hk : KeyPre s₀ b sched)
    (harg : InRegions (s₀.rd ++ s₀.wr) (s₀.ea (argOp 0)) 4) (hr : s₀.mem.readW (s₀.ea (argOp 0)) 32 = sched) :
    ∃ s', runBlock isa (([.mov .ecx (.mem (argOp 0))] : List Instr) ++ kpAt keySlot) s₀ = some s' ∧ s'.gpr .ecx = sched ∧
      AtEntry s' b 0 ∧ (∀ r, r ≠ .ecx → r ≠ kp → s'.gpr r = s₀.gpr r) ∧ s'.mem = s₀.mem ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr := by
  obtain ⟨s₁, e₁, c₁, o₁, m₁, rd₁, wr₁⟩ := ldArg_ok s₀ .ecx 0 harg
  obtain ⟨s₂, e₂, k₂, o₂, m₂, rd₂, wr₂⟩ := kpAt_ok s₁ keySlot
  refine ⟨s₂, by rw [runBlock_app, e₁, Option.bind_some, e₂], by rw [o₂ _ (by decide), c₁, hr], ?_,
    fun r h1 h2 => by rw [o₂ r h2, o₁ r h1], m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁⟩
  rw [AtEntry, k₂, o₁ _ (by decide), hk.base]; rfl

/-- `add ecx, 8` or `sub ecx, 8`, as `keyLoop_wp` takes it. -/
theorem addEcx_op (s : State) : ∃ s', runBlock isa [addI .ecx 8] s = some s' ∧
    s'.gpr .ecx = s.gpr .ecx + 8 ∧ (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e', r', -, o', m', rd', wr'⟩ := addI_ok s .ecx 8
  exact ⟨s', e', r', o', m', rd', wr'⟩

theorem subEcx_op (s : State) : ∃ s', runBlock isa [subI .ecx 8] s = some s' ∧
    s'.gpr .ecx = s.gpr .ecx - 8 ∧ (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e', r', -, o', m', rd', wr'⟩ := subI_ok s .ecx 8
  exact ⟨s', e', r', o', m', rd', wr'⟩

theorem encKeys_wp {s₀ : State} {b sched : BitVec 32} {g : Nat} (hg : g = 3 ∨ g = 4) (hk : KeyPre s₀ b sched)
    (harg : InRegions (s₀.rd ++ s₀.wr) (s₀.ea (argOp 0)) 4) (hr : s₀.mem.readW (s₀.ea (argOp 0)) 32 = sched) :
    WP isa (encKeys g) s₀ (KeysPost s₀ b sched g id) := by
  have hg4 : g ≤ 4 := by omega_arith
  obtain ⟨s₁, e₁, c₁, k₁, o₁, m₁, rd₁, wr₁⟩ := keysSetup_ok hk harg hr
  obtain ⟨s₂, e₂, n₂, o₂, m₂, rd₂, wr₂⟩ := movI_ok s₁ .ebp (BitVec.ofNat 32 (8 * g + 2))
  unfold encKeys
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_app, e₁, Option.bind_some, e₂], ?_⟩)
  have hinv : KeyInv s₀ b sched 0 (8 * g + 2) id (fun i => Spec.Camellia.wordAt s₀.mem
      (sched.setWidth 64 + BitVec.ofNat 64 (8 * i))) 0 s₂ := by
    refine ⟨hk.congr ?_ (rd₂.trans rd₁) (wr₂.trans wr₁), ?_, ?_, ?_, fun i hi => by omega_arith,
      by rw [m₂, m₁]; exact Frame.refl _ _, fun r h1 h2 => ?_, rd₂.trans rd₁, wr₂.trans wr₁⟩
    · rw [o₂ _ (by decide), o₁ _ (by decide) (by decide)]
    · rw [AtEntry, o₂ _ (by decide)]; exact k₁
    · rw [o₂ _ (by decide), c₁]; simp
    · rw [n₂, Nat.sub_zero]
    · rw [o₂ r (fun h => h1 (by rw [h]; decide)), o₁ r (fun h => h1 (by rw [h]; decide)) h2]
  refine WP.mono (keyLoop_wp (e₀ := 0) (N := 8 * g + 2) (wk := id) (f := fun x => x + 8) addEcx_op
    (by omega_arith) (by omega_arith) (fun k hk => by simp; omega_arith) (fun k _ => add8 sched) (fun k _ => by simp) (by omega_arith)
    hinv) fun s h => ?_
  exact ⟨h.pre, fun i hi => h.ent i (by omega_arith), h.frame, h.regs, h.rd, h.wr⟩

/-- `keyOne_step` within the construction of a table from `s₀`. -/
theorem keyOne_inv {s₀ s : State} {b sched : BitVec 32} {d e w : Nat} (hd : d = 0 ∨ d = 8)
    (hk : KeyPre s b sched) (hkp : AtEntry s b e) (he : e < 34)
    (hr : s.gpr .ecx = sched + BitVec.ofNat 32 (8 * w)) (hw : w + d / 8 < 34)
    (hf : Frame [tableRegion b] s₀.mem s.mem) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧ KeyPre s' b sched ∧ AtEntry s' b (e + 1) ∧
      (∀ r, r ∈ [Reg.esp, .esi, .edi, .ecx, .ebp] → r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [tableRegion b] s₀.mem s'.mem ∧
      EntryOk s'.mem b e (Spec.Camellia.wordAt s₀.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * (w + d / 8)))) ∧
      (∀ i < 34, i ≠ e → ∀ j < 16, entryW s'.mem b i j = entryW s.mem b i j) := by
  have hfit := hk.scr.fit
  obtain ⟨s', e', k', o', rd', wr', f', E'⟩ := keyOne_step hd hk hr hw hkp he
  refine ⟨s', e', hk.congr (o' _ (by decide) (by decide)) rd' wr', k', o', rd', wr', ?_, ?_,
    fun i hi hie j hj => entryW_frame hfit f' hi he hie hj⟩
  · exact hf.trans (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, keyRegions_sub hfit he r hr⟩)
  · rw [← hk.wordAt_eq (hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact table_sub_scr⟩) hw]
    exact E'

theorem decKeys_wp {s₀ : State} {b sched : BitVec 32} {g : Nat} (hg : g = 3 ∨ g = 4) (hk : KeyPre s₀ b sched)
    (harg : InRegions (s₀.rd ++ s₀.wr) (s₀.ea (argOp 0)) 4) (hr : s₀.mem.readW (s₀.ea (argOp 0)) 32 = sched) :
    WP isa (decKeys g) s₀ (KeysPost s₀ b sched g (Camellia.decPerm g)) := by
  have hg4 : g ≤ 4 := by omega_arith
  have hg3 : 3 ≤ g := by omega_arith
  unfold decKeys
  -- `kw3`, `kw4` to entries 0 and 1.
  obtain ⟨s₁, e₁, c₁, k₁, o₁, m₁, rd₁, wr₁⟩ := keysSetup_ok hk harg hr
  obtain ⟨s₂, e₂, c₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ .ecx (BitVec.ofNat 32 (64 * g))
  have hk₂ : KeyPre s₂ b sched :=
    hk.congr (by rw [o₂ _ (by decide), o₁ _ (by decide) (by decide)]) (rd₂.trans rd₁) (wr₂.trans wr₁)
  have hkp₂ : AtEntry s₂ b 0 := by rw [AtEntry, o₂ _ (by decide)]; exact k₁
  have hr₂ : s₂.gpr .ecx = sched + BitVec.ofNat 32 (8 * (8 * g)) := by
    rw [c₂, c₁, show 64 * g = 8 * (8 * g) by omega_arith]
  have hf₂ : Frame [tableRegion b] s₀.mem s₂.mem := by rw [m₂, m₁]; exact Frame.refl _ _
  obtain ⟨s₃, e₃, hk₃, kp₃, o₃, rd₃, wr₃, hf₃, E₃, -⟩ :=
    keyOne_inv (s₀ := s₀) (d := 0) (Or.inl rfl) hk₂ hkp₂ (by omega_arith) hr₂ (by omega_arith) hf₂
  obtain ⟨s₄, e₄, hk₄, kp₄, o₄, rd₄, wr₄, hf₄, E₄, P₄⟩ :=
    keyOne_inv (s₀ := s₀) (d := 8) (Or.inr rfl) hk₃ kp₃ (by omega_arith)
      (by rw [o₃ _ (by decide) (by decide), hr₂]) (by omega_arith) hf₃
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := subEcx_op s₄
  obtain ⟨s₆, e₆, n₆, o₆, m₆, rd₆, wr₆⟩ := movI_ok s₅ .ebp (BitVec.ofNat 32 (8 * g - 2))
  have hr₆ : s₆.gpr .ecx = sched + BitVec.ofNat 32 (8 * (8 * g - 1)) := by
    rw [o₆ _ (by decide), r₅, o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), hr₂]
    have := sub8 sched (w := 8 * g - 1)
    rwa [show 8 * g - 1 + 1 = 8 * g by omega_arith] at this
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some,
      show ([subI .ecx 8, movI .ebp (BitVec.ofNat 32 (8 * g - 2))] : List Instr) =
        [subI .ecx 8] ++ [movI .ebp (BitVec.ofNat 32 (8 * g - 2))] from rfl,
      runBlock_app, e₅, Option.bind_some, e₆], ?_⟩)
  -- The loop: entries 2 to `8 g - 1`.
  let F : Nat → BitVec 64 := fun i =>
    Spec.Camellia.wordAt s₀.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * Camellia.decPerm g i))
  have hF0 : F 0 = Spec.Camellia.wordAt s₀.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * (8 * g + 0 / 8))) := by
    simp [F, Camellia.decPerm]
  have hF1 : F 1 = Spec.Camellia.wordAt s₀.mem (sched.setWidth 64 + BitVec.ofNat 64 (8 * (8 * g + 8 / 8))) := by
    simp [F, Camellia.decPerm]
  have hm₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  have hinv : KeyInv s₀ b sched 2 (8 * g - 2) (fun k => 8 * g - 1 - k) F 0 s₆ := by
    refine ⟨hk₄.congr ?_ ?_ ?_, ?_, by rw [hr₆, Nat.sub_zero], by rw [n₆, Nat.sub_zero],
      fun i hi => ?_, by rw [hm₆]; exact hf₄, fun r h1 h2 => ?_, by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
      by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
    · rw [o₆ _ (by decide), o₅ _ (by decide)]
    · rw [rd₆, rd₅]
    · rw [wr₆, wr₅]
    · rw [AtEntry, o₆ _ (by decide), o₅ _ (by decide)]; exact kp₄
    · rw [hm₆]
      rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl
      · rw [hF0]; exact E₃.congr fun j hj => P₄ 0 (by omega_arith) (by omega_arith) j hj
      · rw [hF1]; exact E₄
    · have hk' := keep_regs h1
      rw [o₆ r (fun h => h1 (by rw [h]; decide)), o₅ r (fun h => h1 (by rw [h]; decide)),
        o₄ r hk' h2, o₃ r hk' h2, o₂ r (fun h => h1 (by rw [h]; decide)),
        o₁ r (fun h => h1 (by rw [h]; decide)) h2]
  refine WP.seq (WP.mono (keyLoop_wp (e₀ := 2) (N := 8 * g - 2) (wk := fun k => 8 * g - 1 - k)
    (f := fun x => x - 8) subEcx_op (by omega_arith) (by omega_arith)
    (fun k hk => by omega_arith) (fun k hk => ?_) (fun k hk => ?_) (by omega_arith) hinv) fun s h => ?_)
  · have := sub8 sched (w := 8 * g - 1 - (k + 1))
    rwa [show 8 * g - 1 - (k + 1) + 1 = 8 * g - 1 - k by omega_arith] at this
  · simp only [F, Camellia.decPerm, show ¬ 2 + k < 2 by omega_arith, show 2 + k < 8 * g by omega_arith, ↓reduceIte,
      show 8 * g + 1 - (2 + k) = 8 * g - 1 - k by omega_arith]
  -- `kw1`, `kw2` to entries `8 g` and `8 g + 1`.
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := subEcx_op s
  have hr₇ : s₇.gpr .ecx = sched + BitVec.ofNat 32 (8 * 0) := by
    rw [r₇, h.ptr, show 8 * g - 1 - (8 * g - 2) = 0 + 1 by omega_arith]
    exact sub8 sched
  have hk₇ : KeyPre s₇ b sched := h.pre.congr (o₇ _ (by decide)) rd₇ wr₇
  have hkp₇ : AtEntry s₇ b (8 * g) := by
    rw [AtEntry, o₇ _ (by decide)]
    have := h.kpos
    rwa [show 2 + (8 * g - 2) = 8 * g by omega_arith] at this
  obtain ⟨s₈, e₈, hk₈, kp₈, o₈, rd₈, wr₈, hf₈, E₈, P₈⟩ :=
    keyOne_inv (s₀ := s₀) (d := 0) (Or.inl rfl) hk₇ hkp₇ (by omega_arith) hr₇ (by omega_arith) (by rw [m₇]; exact h.frame)
  obtain ⟨s₉, e₉, hk₉, -, o₉, rd₉, wr₉, hf₉, E₉, P₉⟩ :=
    keyOne_inv (s₀ := s₀) (d := 8) (Or.inr rfl) hk₈ kp₈ (by omega_arith)
      (by rw [o₈ _ (by decide) (by decide), hr₇]) (by omega_arith) hf₈
  refine WP.of_runBlock ⟨s₉, by
    rw [runBlock_app, runBlock_app, e₇, Option.bind_some, e₈, Option.bind_some, e₉],
    hk₉, fun i hi => ?_, hf₉, fun r h1 h2 => ?_, by rw [rd₉, rd₈, rd₇, h.rd], by rw [wr₉, wr₈, wr₇, h.wr]⟩
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
  · have hk' := keep_regs h1
    rw [o₉ r hk' h2, o₈ r hk' h2, o₇ r (fun h => h1 (by rw [h]; decide)), h.regs r h1 h2]

end VG.Proof.Camellia.X86
