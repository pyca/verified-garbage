module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Prologue
public import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Impl.Camellia.RISCV64.Ecb
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Camellia.RISCV64.Linear

/-! ### `Camellia.RISCV64.KeyChecks`, which this module and modules that import it used -/

section

/-!
# Bitslicing a subkey on RISC-V, by evaluation

As on PPC64LE (`Proof/Camellia/PPC64LE/KeyChecks.lean`): `keyOne d` loads
the subkey at `[a0 + d]` (a byte at a time, `Words64.loadLE64_ok`) into
`q 0`, copies it to the other state registers and bitslices them as `toBs`
does eight blocks' halves (`keyRest`), and stores the planes to the entry
at `kp` (`keyStore`). Both are checked over the lane domain: the subkey is
input word 0 (in `q 0`), and the planes are input words `0 … 7` of the
stores.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 t2 kp movR)
open VG.Proof.Camellia (pos)

/-- The masks' slots below the saved registers. -/
def keyCfg : Cfg := { base := sb, slots := savedSlot, ext := sb, exts := 0 }

def keyRest : List Instr := ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++ toBs

def keyStore : List Instr := (List.range 8).map fun j => .store .d (q j) kp (8 * j)

theorem keyOne_eq (d : Nat) :
    keyOne d = Impl.Words64.RISCV64.loadLE64 (q 0) t0 t2 .a0 d ++ keyRest ++ keyStore ++
      ([.addi kp kp 64] : List Instr) := by
  simp only [keyOne, keyRest, keyStore, List.append_assoc]

def keyEnv : Env (Nat × Nat) := linEnvG [(q 0, 0)] [] allMasks

/-- Plane `j` of the subkey: bit `8 c + b` is bit `j` of its byte `pos c`. -/
def keyBsG (j p : Nat) : List Nat := [8 * pos (p / 8) + j]

theorem keyRest_check :
    check (lanes 64 7) keyCfg (linExt 0) keyRest keyEnv
      (linPostG 7 (qOuts keyBsG) [] maskSlots keyEnv) = true := by
  decide +kernel

/-- The entry at `kp`. -/
def entryCfg : Cfg := { base := kp, slots := 8, ext := kp, exts := 0 }

def entryEnv : Env (Nat × Nat) := linEnvG qIns [] []

theorem keyStore_check :
    check (lanes 64 9) entryCfg (linExt 0) keyStore entryEnv
      (linPostG 9 [] ((List.range 8).map fun j => (j, fun p => [64 * j + p])) [] entryEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.RISCV64

end

end

/-! ### `Camellia.RISCV64.Keys`, which this module and modules that import it used -/

section

/-!
# The table of bitsliced subkeys on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/Group.lean`): `keyOne_step`:
`keyOne d` bitslices the subkey at `[a0 + d]` (its eight bytes, the most
significant first: `wordAt`) into the table's entry at `kp`, every block's
copy of it alike, and steps `kp` to the next entry. `encKeys_wp` and
`decKeys_wp` build the table in the order the rounds use the subkeys: for
encryption the stored order, for decryption `decPerm`'s. They write only
the rounds' working space and the table (`keyRegions`), not the saved
registers and the tail buffer between them.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 t2 kp movR)
open VG.Proof.Aes.RISCV64 (sboxWrites not_sboxWrites restRegs)
open VG.Proof.Camellia (HalfRel WordRel pos)

/-! ## Steps of the pointers and the counters -/

theorem addI_ok (s : State) (d n : Reg) (imm : Nat) (h : imm < 2048) :
    ∃ s', runBlock isa [.addi d n (OfNat.ofNat imm)] s = some s' ∧ s'.gpr d = s.gpr n + BitVec.ofNat 64 imm ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.gpr n + BitVec.ofNat 64 imm), by
    simp only [runBlock_cons, exec_addi (show imm12 (OfNat.ofNat imm : Int) by
        show imm12 ((imm : Nat) : Int); unfold imm12; omega_using [h]), runStep_some, runBlock_nil]
    rw [show (OfNat.ofNat imm : Int) = ((imm : Nat) : Int) from rfl, Steps.ofInt_ofNat],
    RegUpd.gpr_write_self _ _ _, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

theorem subI_ok (s : State) (d n : Reg) (imm : Nat) (h : imm ≤ 2048) :
    ∃ s', runBlock isa [.addi d n (-(OfNat.ofNat imm))] s = some s' ∧
      s'.gpr d = s.gpr n - BitVec.ofNat 64 imm ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.gpr n - BitVec.ofNat 64 imm), by
    simp only [runBlock_cons, exec_addi (show imm12 (-(OfNat.ofNat imm) : Int) by
        show imm12 (-((imm : Nat) : Int)); unfold imm12; omega_using [h]), runStep_some, runBlock_nil]
    rw [show (-(OfNat.ofNat imm) : Int) = -((imm : Nat) : Int) from rfl, Steps.add_ofInt_neg],
    RegUpd.gpr_write_self _ _ _, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- `li d, v`. -/
theorem li_ok (s : State) (d : Reg) {v : Nat} (hv : v < 2048) :
    ∃ s', runBlock isa [.li d (v : Int)] s = some s' ∧ s'.gpr d = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (BitVec.ofNat 64 v), by
    simp only [runBlock_cons, exec_li (show imm12 ((v : Nat) : Int) by unfold imm12; omega_using [hv]), runStep_some,
      runBlock_nil, Steps.ofInt_ofNat],
    RegUpd.gpr_write_self _ _ _, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-! ## One subkey -/

/-- The table's entry `e` holds `k` for every block. -/
abbrev EntryOk (m : Mem) (b : Addr) (e : Nat) (k : BitVec 64) : Prop := HalfRel (entryW m b e) fun _ => k

theorem keyOne_step {s : State} {b : Addr} {d e : Nat} (hd : d = 0 ∨ d = 8)
    (hb : s.gpr sb = b) (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hal : b.toNat % 8 = 0)
    (hkp : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e)) (he : e < 34)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 d) 8) (hm : MasksOk s) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 ∧ (∀ r, r ∉ sboxWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.gpr t1 = s.gpr t1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧
      Frame [⟨b, 8 * savedSlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64⟩] s.mem s'.mem ∧
      EntryOk s'.mem b e (Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 d)) := by
  rw [slots_eq] at hscr
  -- The load.
  obtain ⟨s₀, e₀, u₀⟩ := WP.runBlock_of (Words64.loadLE64_ok (s := s) (d := q 0) (tmp := t0) (tmp2 := t2)
    (n := .a0) (off := d) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rcases hd with rfl | rfl <;> decide) hin)
  have k₀ : ∀ r, r ∉ sboxWrites → s₀.gpr r = s.gpr r := fun r hr =>
    u₀.other r (fun h => hr (by subst h; decide)) (fun h => hr (by subst h; decide))
      (fun h => hr (by subst h; decide))
  have hb₀ : s₀.gpr sb = b := by rw [k₀ sb (by decide), hb]
  have hm₀ : MasksOk s₀ := fun kv hkv => by
    show s₀.mem.readW (wordAddr (s₀.gpr sb) kv.1) 64 = kv.2
    rw [u₀.mem, k₀ sb (by decide)]; exact hm kv hkv
  -- The planes.
  have hok : Ok keyCfg s₀ :=
    { slotIn := fun k hk => ⟨_, by rw [u₀.wr]; exact hscr, by
        simp only [keyCfg, savedSlot_eq] at hk ⊢
        rw [hb₀]; exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)⟩
      extIn := fun k hk => by simp [keyCfg] at hk
      baseAl := fun _ => by simp only [keyCfg]; rw [hb₀]; exact hal
      extAl := fun h => by simp [keyCfg] at h
      slots := by simp [keyCfg, savedSlot_eq]
      sep := fun k _ j hj => by simp [keyCfg] at hj }
  have hchk := keyRest_check
  unfold keyEnv at hchk
  obtain ⟨s₁, e₁, ho₁, -, hkp₁, rd₁, wr₁, -, o₁, f₁, hb₁, -⟩ := linG_ok hchk hok
    (fun _ => s₀.gpr (q 0))
    (fun r i hri => by
      simp only [List.mem_singleton, Prod.mk.injEq] at hri
      obtain ⟨rfl, rfl⟩ := hri; exact ⟨by decide, rfl⟩)
    (fun j i hji => by simp at hji)
    (fun kv hkv => ⟨by simp only [keyCfg]; exact mask_lt hkv, by
      simp only [keyCfg]; exact hm₀ kv hkv⟩)
    (fun j hj => by simp [keyCfg] at hj)
  simp only [keyCfg] at hb₁ hkp₁ f₁
  have hall₁ : ∀ r, r ∉ sboxWrites → (keyRest.all fun i => dst i != some r) = true := fun r hr => by
    have h := not_sboxWrites r hr
    have : (restRegs.all fun r => keyRest.all fun i => dst i != some r) = true := by decide +kernel
    exact List.all_eq_true.mp this r h
  have k₁ : ∀ r, r ∉ sboxWrites → s₁.gpr r = s₀.gpr r := fun r hr => o₁ r (hall₁ r hr)
  have hQ : HalfRel (Qs s₁) (fun _ => Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 d)) := by
    have hw := wordRel_key s.mem (s.gpr .a0 + BitVec.ofNat 64 d)
    refine Camellia.half_of_words (W := fun _ => s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 d) 64)
      (fun j hj p hp => ?_) hw
    have := Camellia.pos_lt (show p / 8 < 8 by omega_arith)
    rw [Qs, ho₁ (q j) (keyBsG j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false,
      show 8 * pos (p / 8) + j = 64 * 0 + (8 * pos (p / 8) + j) by omega_arith,
      bitOf_word _ _ _ (by omega_arith), u₀.gpr, Nat.zero_add]
  -- The stores.
  have hkp₁' : s₁.gpr kp = s.gpr kp := by rw [k₁ kp (by decide), k₀ kp (by decide)]
  have hok₂ : Ok entryCfg s₁ :=
    { slotIn := fun k hk => ⟨_, by rw [wr₁, u₀.wr]; exact hscr, by
        simp only [entryCfg] at hk ⊢
        rw [hkp₁', hkp, wordAddr, addr_add]
        exact VG.Offset.contains_base b (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)⟩
      extIn := fun k hk => by simp [entryCfg] at hk
      baseAl := fun _ => by
        simp only [entryCfg]; rw [hkp₁', hkp]; exact Spill.al8 hal (by omega_arith)
      extAl := fun h => by simp [entryCfg] at h
      slots := by simp [entryCfg]
      sep := fun k _ j hj => by simp [entryCfg] at hj }
  have hchk₂ := keyStore_check
  unfold entryEnv at hchk₂
  obtain ⟨s₂, e₂, -, hso₂, -, rd₂, wr₂, -, o₂, f₂, hb₂, -⟩ := linG_ok hchk₂ hok₂ (Qs s₁)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, rfl⟩)
    (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [entryCfg] at hj)
  simp only [entryCfg] at hb₂ hso₂ f₂
  have hall₂ : ∀ r, (keyStore.all fun i => dst i != some r) = true := fun r => by
    cases r <;> rfl
  have k₂ : ∀ r, s₂.gpr r = s₁.gpr r := fun r => o₂ r (hall₂ r)
  obtain ⟨s₃, e₃, kp₃, o₃, m₃, rd₃, wr₃⟩ := addKp_ok s₂ 64 (by decide)
  have he₂ : ∀ j < 8, entryW s₂.mem b e j = Qs s₁ j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    have h := hso₂ j (fun p => [64 * j + p]) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      hj p hp
    rw [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp] at h
    rw [← h, entryW, wordAddr, hkp₁', hkp, addr_add]
  have ht1 : s₁.gpr t1 = s.gpr t1 := by
    rw [o₁ t1 (by decide +kernel), u₀.other _ (by decide) (by decide) (by decide)]
  refine ⟨s₃, ?_, ?_, fun r h1 h2 => ?_, by rw [o₃ t1 (by decide), k₂, ht1], by rw [rd₃, rd₂, rd₁, u₀.rd],
    by rw [wr₃, wr₂, wr₁, u₀.wr], fun kv hkv => ?_, ?_, ?_⟩
  · rw [keyOne_eq, runBlock_append', runBlock_append', runBlock_append', e₀, Option.bind_some, e₁,
      Option.bind_some, e₂, Option.bind_some]
    exact e₃
  · rw [kp₃, k₂, hkp₁']
  · rw [o₃ r h2, k₂, k₁ r h1, k₀ r h1]
  · have hk : kv.1 < savedSlot := mask_lt hkv
    show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
    have h2 : s₂.mem.readW (wordAddr b kv.1) 64 = s₁.mem.readW (wordAddr b kv.1) 64 := by
      refine f₂.readW (r := ⟨wordAddr b kv.1, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [slotRegion, List.mem_singleton] at hr; subst hr
      rw [hkp₁', hkp, wordAddr]
      exact VG.Offset.disjoint b (Or.inl (by rw [keySlot_eq]; rw [savedSlot_eq] at hk; omega_arith))
        (by rw [savedSlot_eq] at hk; omega_arith) (by rw [keySlot_eq]; omega_arith)
    rw [m₃, o₃ sb (by decide), k₂, hb₁, hb₀, h2, ← hb₀, hkp₁ kv.1 (List.mem_map_of_mem hkv) hk]
    exact hm₀ kv hkv
  · rw [m₃, ← u₀.mem]
    refine (f₁.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr; simp [hb₀]
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr
      simp [hkp₁', hkp]
  · refine hQ.congr fun j hj => ?_
    show entryW s₃.mem b e j = _
    rw [m₃]; exact he₂ j hj

/-! ## The loops -/

/-- What the table's construction writes in the scratch buffer at `b`: the
rounds' working space and the table. -/
def keyRegions (b : Addr) : List Region :=
  [⟨b, 8 * savedSlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot), 8 * (slots - keySlot)⟩]

/-- The scratch buffer at `b` and the schedule's 34 words at `sched`, apart. -/
structure KeyPre (s : State) (b sched : Addr) : Prop where
  base : s.gpr sb = b
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr
  al : b.toNat % 8 = 0
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  sch : (⟨sched, 272⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 272 ≤ 2 ^ 64
  sep : Region.Disjoint ⟨sched, 272⟩ ⟨b, 8 * slots⟩

theorem KeyPre.congr {s s' : State} {b sched : Addr} (h : KeyPre s b sched) (hb : s'.gpr sb = s.gpr sb)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : KeyPre s' b sched :=
  ⟨hb.trans h.base, hwr ▸ h.scr, h.al, h.fit, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

/-- The eight bytes `d` bytes into word `w` of the schedule. -/
theorem KeyPre.inSub {s : State} {b sched : Addr} (h : KeyPre s b sched) {w d : Nat}
    (hw : 8 * w + d + 8 ≤ 272) :
    InRegions (s.rd ++ s.wr) (sched + BitVec.ofNat 64 (8 * w) + BitVec.ofNat 64 d) 8 :=
  ⟨_, h.sch, by rw [addr_add]; exact VG.Offset.contains_base sched (by omega_arith) (by omega_arith)⟩

/-- The schedule is outside the scratch buffer. -/
theorem KeyPre.wordAt_eq {s : State} {b sched : Addr} (h : KeyPre s b sched) {m m' : Mem}
    (hf : Frame (keyRegions b) m m') {w : Nat} (hw : w < 34) :
    Spec.Camellia.wordAt m' (sched + BitVec.ofNat 64 (8 * w)) =
      Spec.Camellia.wordAt m (sched + BitVec.ofNat 64 (8 * w)) := by
  refine wordAt_frame hf fun r hr => ?_
  have hs := h.sep.sub_left (VG.Offset.sub_base sched (d := 8 * w) (n := 8) (by omega_arith))
  simp only [keyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.sub_right (Region.sub_prefix (by rw [savedSlot_eq, slots_eq]; omega_arith))
  · exact hs.sub_right (VG.Offset.sub_base b (by decide))

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : Addr} {e i : Nat}
    (hf : Frame [⟨b, 8 * savedSlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64⟩] m m')
    (hi : i < 34) (he : e < 34) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base b (by rw [keySlot_eq, savedSlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)
  · exact VG.Offset.disjoint b (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)
      (by rw [keySlot_eq]; omega_arith)

/-- One step's frame, within `keyRegions`. -/
theorem keyRegions_sub (b : Addr) {e : Nat} (he : e < 34) :
    ∀ r ∈ ([⟨b, 8 * savedSlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64⟩] : List Region),
      ∃ r' ∈ keyRegions b, Region.Sub r r' := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (Nat.le_refl _)⟩
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
    rw [← addr_add]
    exact VG.Offset.sub_base _ (by rw [slots_eq, keySlot_eq]; omega_arith)

/-- What the loops keep, after `k` of their `N` iterations: the subkeys `F`
in the entries before `e₀ + k`, `a0` at word `wk k` of the schedule. -/
structure KeyInv (s₀ : State) (b sched : Addr) (e₀ N : Nat) (wk : Nat → Nat) (F : Nat → BitVec 64)
    (k : Nat) (s : State) : Prop where
  pre : KeyPre s b sched
  kpos : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e₀ + k))
  a0 : s.gpr .a0 = sched + BitVec.ofNat 64 (8 * wk k)
  cnt : s.gpr t1 = BitVec.ofNat 64 (N - k)
  ent : ∀ i < e₀ + k, EntryOk s.mem b i (F i)
  masks : MasksOk s
  frame : Frame (keyRegions b) s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loop of `keyOne 0` and `op a0, a0, 8` (`f` on `a0`), counted down in `t1`. -/
theorem keyLoop_wp {s₀ s : State} {b sched : Addr} {e₀ N : Nat} {wk : Nat → Nat} {F : Nat → BitVec 64}
    {i₁ : Instr} {f : Addr → Addr}
    (hop : ∀ s : State, ∃ s', runBlock isa [i₁] s = some s' ∧
      s'.gpr .a0 = f (s.gpr .a0) ∧ (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (hN : e₀ + N ≤ 34)
    (hwk : ∀ k < N, wk k < 34)
    (hstep : ∀ k < N, f (sched + BitVec.ofNat 64 (8 * wk k)) = sched + BitVec.ofNat 64 (8 * wk (k + 1)))
    (hF : ∀ k < N, F (e₀ + k) = Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * wk k)))
    {k : Nat} (hk : k < N) (hs : KeyInv s₀ b sched e₀ N wk F k s) :
    WP isa (.loop (.block (keyOne 0 ++ ([i₁, .addi t1 t1 (-1)] : List Instr))) (.nonzero t1)) s
      (KeyInv s₀ b sched e₀ N wk F N) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = N - k ∧ k < N ∧ KeyInv s₀ b sched e₀ N wk F k s)
    (fun n s hs => ?_) (N - k) s ⟨k, rfl, hk, hs⟩
  obtain ⟨k, rfl, hk, hi⟩ := hs
  have hw := hwk k hk
  have hr3 := hi.a0
  obtain ⟨s₁, e₁, kp₁, o₁, t₁, rd₁, wr₁, m₁, f₁, E₁⟩ := keyOne_step (d := 0) (e := e₀ + k) (Or.inl rfl)
    hi.pre.base hi.pre.scr hi.pre.al hi.kpos (by omega_arith)
    (by rw [hr3]; exact hi.pre.inSub (by omega_arith)) hi.masks
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := hop s₁
  obtain ⟨s₃, e₃, c₃, o₃, m₃, rd₃, wr₃⟩ := subI_ok s₂ t1 t1 1 (by decide)
  refine WP.of_runBlock ⟨s₃, by
    rw [runBlock_append', e₁, Option.bind_some,
      show ([i₁, .addi t1 t1 (-1)] : List Instr) = [i₁] ++ [.addi t1 t1 (-1)] from rfl,
      runBlock_append', e₂, Option.bind_some]
    exact e₃, ?_⟩
  have ht₂ : s₂.gpr t1 = BitVec.ofNat 64 (N - k) := by rw [o₂ _ (by decide), t₁, hi.cnt]
  have hc₃ : s₃.gpr t1 = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [c₃, ht₂, VG.Offset.ofNat_sub_ofNat (by omega_arith), show N - k - 1 = N - (k + 1) by omega_arith]
  -- The new invariant.
  have hf₁₃ : Frame [⟨b, 8 * savedSlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * (e₀ + k)), 64⟩]
      s.mem s₃.mem := by
    rw [m₃, m₂]; exact f₁
  have hinv : KeyInv s₀ b sched e₀ N wk F (k + 1) s₃ := by
    refine ⟨hi.pre.congr ?_ ?_ ?_, ?_, ?_, hc₃, fun i hi' => ?_, fun kv hkv => ?_, ?_, fun r h1 h2 h3 => ?_,
      by rw [rd₃, rd₂, rd₁, hi.rd], by rw [wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide) (by decide)]
    · rw [rd₃, rd₂, rd₁]
    · rw [wr₃, wr₂, wr₁]
    · rw [o₃ _ (by decide), o₂ _ (by decide), kp₁, hi.kpos, addr_add,
        show 8 * keySlot + 64 * (e₀ + k) + 64 = 8 * keySlot + 64 * (e₀ + (k + 1)) by omega_arith]
    · rw [o₃ _ (by decide), r₂, o₁ _ (by decide) (by decide), hr3, hstep k hk]
    · by_cases he : i = e₀ + k
      · subst he
        have hw' : Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 0) = F (e₀ + k) := by
          rw [hr3, addr_add, Nat.add_zero, hF k hk]
          exact hi.pre.wordAt_eq hi.frame hw
        rw [← hw']
        exact E₁.congr fun j _ => by
          show entryW s₃.mem b (e₀ + k) j = entryW s₁.mem b (e₀ + k) j
          rw [m₃, m₂]
      · refine (hi.ent i (by omega_arith)).congr fun j hj => ?_
        exact entryW_frame hf₁₃ (by omega_arith) (by omega_arith) he hj
    · show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
      rw [m₃, m₂, o₃ _ (by decide), o₂ _ (by decide)]; exact m₁ kv hkv
    · exact hi.frame.trans ((f₁.sub (keyRegions_sub b (by omega_arith))).trans
        (by rw [m₃, m₂]; exact Frame.refl _ _))
    · rw [o₃ r (fun h => h1 (by subst h; decide)), o₂ r h3, o₁ r h1 h2, hi.regs r h1 h2 h3]
  have hz : (s₃.gpr t1 == 0) = decide (N - (k + 1) = 0) := by
    rw [hc₃, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, Bool.eq_iff_iff, beq_iff_eq,
      decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega_arith
    · intro h; rw [h]
  by_cases hl : k + 1 = N
  · refine .inl ⟨(eval_nonzero s₃ t1).trans (by rw [hz]; simp; omega_arith),
      by rw [show k + 1 = N from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_nonzero s₃ t1).trans (by rw [hz]; simp; omega_arith), N - (k + 1), by omega_arith, k + 1, rfl,
      by omega_arith, hinv⟩

/-! ## The tables -/

/-- What the table's construction leaves: entry `i` holds word `perm i` of the schedule. -/
structure KeysPost (s₀ : State) (b sched : Addr) (g : Nat) (perm : Nat → Nat) (s : State) : Prop where
  pre : KeyPre s b sched
  ent : ∀ i < 8 * g + 2,
    EntryOk s.mem b i (Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * perm i)))
  masks : MasksOk s
  frame : Frame (keyRegions b) s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → r ≠ .a4 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem add8 (x : Addr) {w : Nat} :
    x + BitVec.ofNat 64 (8 * w) + BitVec.ofNat 64 8 = x + BitVec.ofNat 64 (8 * (w + 1)) := by
  rw [addr_add, show 8 * w + 8 = 8 * (w + 1) by omega_arith]

theorem sub8 (x : Addr) {w : Nat} :
    x + BitVec.ofNat 64 (8 * (w + 1)) - BitVec.ofNat 64 8 = x + BitVec.ofNat 64 (8 * w) := by
  rw [VG.Offset.add_ofNat_sub _ (by omega_arith), show 8 * (w + 1) - 8 = 8 * w by omega_arith]

theorem encKeys_wp {s₀ : State} {b sched : Addr} {g : Nat} (hg : g = 3 ∨ g = 4) (hk : KeyPre s₀ b sched)
    (hr3 : s₀.gpr .a0 = sched) (ht1 : s₀.gpr t1 = BitVec.ofNat 64 (8 * g + 2)) (hm : MasksOk s₀) :
    WP isa encKeys s₀ fun s => KeysPost s₀ b sched g id s ∧ s.gpr .a4 = s₀.gpr .a4 := by
  have hg4 : g ≤ 4 := by omega_arith
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁⟩ := setKp_ok s₀
  unfold encKeys
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have hinv : KeyInv s₀ b sched 0 (8 * g + 2) id (fun i => Spec.Camellia.wordAt s₀.mem
      (sched + BitVec.ofNat 64 (8 * i))) 0 s₁ := by
    refine ⟨hk.congr ?_ rd₁ wr₁, ?_, ?_, ?_, fun i hi => by omega_arith, fun kv hkv => ?_, ?_, fun r h1 h2 _ => o₁ r h2,
      rd₁, wr₁⟩
    · rw [o₁ _ (by decide)]
    · rw [k₁, hk.base]; simp
    · rw [o₁ _ (by decide), hr3]; simp
    · rw [o₁ _ (by decide), ht1, Nat.sub_zero]
    · show s₁.mem.readW (wordAddr (s₁.gpr sb) kv.1) 64 = kv.2
      rw [m₁, o₁ _ (by decide)]; exact hm kv hkv
    · rw [m₁]; exact Frame.refl _ _
  refine WP.mono (keyLoop_wp (e₀ := 0) (N := 8 * g + 2) (wk := id) (f := fun x => x + BitVec.ofNat 64 8)
    (fun s => addI_ok s .a0 .a0 8 (by decide)) (by omega_arith) (fun k hk => by simp; omega_arith)
    (fun k _ => add8 sched) (fun k _ => by simp) (by omega_arith) hinv) fun s h => ?_
  exact ⟨⟨h.pre, fun i hi => h.ent i (by omega_arith), h.masks, h.frame, fun r h1 h2 h3 _ => h.regs r h1 h2 h3,
    h.rd, h.wr⟩, h.regs _ (by decide) (by decide) (by decide)⟩

/-- `keyOne_step` within the construction of a table from `s₀`. -/
theorem keyOne_inv {s₀ s : State} {b sched : Addr} {d e w : Nat} (hd : d = 0 ∨ d = 8)
    (hk : KeyPre s b sched) (hkp : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e)) (he : e < 34)
    (hr3 : s.gpr .a0 = sched + BitVec.ofNat 64 (8 * w)) (hw : w + d / 8 < 34) (hm : MasksOk s)
    (hf : Frame (keyRegions b) s₀.mem s.mem) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧ KeyPre s' b sched ∧
      s'.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e + 1)) ∧
      (∀ r, r ∉ sboxWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.gpr t1 = s.gpr t1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧ Frame (keyRegions b) s₀.mem s'.mem ∧
      EntryOk s'.mem b e (Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (w + d / 8)))) ∧
      (∀ i < 34, i ≠ e → ∀ j < 8, entryW s'.mem b i j = entryW s.mem b i j) := by
  obtain ⟨s', e', k', o', t', rd', wr', m', f', E'⟩ := keyOne_step hd hk.base hk.scr hk.al hkp he
    (by rw [hr3]; exact hk.inSub (by rcases hd with rfl | rfl <;> omega_arith)) hm
  refine ⟨s', e', hk.congr (o' _ (by decide) (by decide)) rd' wr', ?_, o', t', rd', wr', m',
    hf.trans (f'.sub (keyRegions_sub b he)), ?_, fun i hi hie j hj => entryW_frame f' hi he hie hj⟩
  · rw [k', hkp, addr_add, show 8 * keySlot + 64 * e + 64 = 8 * keySlot + 64 * (e + 1) by omega_arith]
  · have hw' : Spec.Camellia.wordAt s.mem (s.gpr .a0 + BitVec.ofNat 64 d) =
        Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (w + d / 8))) := by
      rw [hr3, addr_add, show 8 * w + d = 8 * (w + d / 8) by omega_arith]
      exact hk.wordAt_eq hf hw
    rw [← hw']; exact E'

theorem decKeys_wp {s₀ : State} {b sched : Addr} {g : Nat} (hg : g = 3 ∨ g = 4) (hk : KeyPre s₀ b sched)
    (hr3 : s₀.gpr .a0 = sched + BitVec.ofNat 64 (8 * (8 * g))) (ht1 : s₀.gpr t1 = BitVec.ofNat 64 (8 * g - 2))
    (hm : MasksOk s₀) :
    WP isa decKeys s₀ fun s => KeysPost s₀ b sched g (Camellia.decPerm g) s ∧ s.gpr .a4 = s₀.gpr .a4 := by
  have hg4 : g ≤ 4 := by omega_arith
  have hg3 : 3 ≤ g := by omega_arith
  unfold decKeys
  -- `kw3`, `kw4` to entries 0 and 1.
  obtain ⟨s₂, e₂, k₂, o₂, m₂, rd₂, wr₂⟩ := setKp_ok s₀
  have hr3₂ : s₂.gpr .a0 = sched + BitVec.ofNat 64 (8 * (8 * g)) := by rw [o₂ _ (by decide), hr3]
  have hk₂ : KeyPre s₂ b sched := hk.congr (o₂ _ (by decide)) rd₂ wr₂
  have hm₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, o₂ _ (by decide)]; exact hm kv hkv
  have hf₂ : Frame (keyRegions b) s₀.mem s₂.mem := by rw [m₂]; exact Frame.refl _ _
  have hkp₂ : s₂.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * 0) := by
    rw [k₂, hk.base]; simp
  obtain ⟨s₃, e₃, hk₃, kp₃, o₃, t₃, rd₃, wr₃, hm₃, hf₃, E₃, -⟩ :=
    keyOne_inv (d := 0) (Or.inl rfl) hk₂ hkp₂ (by omega_arith) hr3₂ (by omega_arith) hm₂ hf₂
  obtain ⟨s₄, e₄, hk₄, kp₄, o₄, t₄, rd₄, wr₄, hm₄, hf₄, E₄, P₄⟩ :=
    keyOne_inv (d := 8) (Or.inr rfl) hk₃ kp₃ (by omega_arith) (by rw [o₃ _ (by decide) (by decide), hr3₂])
      (by omega_arith) hm₃ hf₃
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := subI_ok s₄ .a0 .a0 8 (by decide)
  have hr3₆ : s₆.gpr .a0 = sched + BitVec.ofNat 64 (8 * (8 * g - 1)) := by
    rw [r₆, o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), hr3₂]
    have := sub8 sched (w := 8 * g - 1)
    rwa [show 8 * g - 1 + 1 = 8 * g by omega_arith] at this
  have t₆ : s₆.gpr t1 = BitVec.ofNat 64 (8 * g - 2) := by
    rw [o₆ _ (by decide), t₄, t₃, o₂ _ (by decide), ht1]
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [runBlock_append', runBlock_append', runBlock_append', e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some, e₆], ?_⟩)
  -- The loop: entries 2 to `8 g - 1`.
  let F : Nat → BitVec 64 := fun i =>
    Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * Camellia.decPerm g i))
  have hF0 : F 0 = Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (8 * g + 0 / 8))) := by
    simp [F, Camellia.decPerm]
  have hF1 : F 1 = Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (8 * g + 8 / 8))) := by
    simp [F, Camellia.decPerm]
  have hinv : KeyInv s₀ b sched 2 (8 * g - 2) (fun k => 8 * g - 1 - k) F 0 s₆ := by
    refine ⟨hk₄.congr ?_ ?_ ?_, ?_, by rw [hr3₆, Nat.sub_zero], by rw [t₆, Nat.sub_zero], fun i hi => ?_,
      fun kv hkv => ?_, by rw [m₆]; exact hf₄, fun r h1 h2 h3 => ?_, by rw [rd₆, rd₄, rd₃, rd₂],
      by rw [wr₆, wr₄, wr₃, wr₂]⟩
    · rw [o₆ _ (by decide)]
    · rw [rd₆]
    · rw [wr₆]
    · rw [o₆ _ (by decide), kp₄]
    · have hmem : s₆.mem = s₄.mem := m₆
      rw [hmem]
      rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl
      · rw [hF0]; exact E₃.congr fun j hj => P₄ 0 (by omega_arith) (by omega_arith) j hj
      · rw [hF1]; exact E₄
    · show s₆.mem.readW (wordAddr (s₆.gpr sb) kv.1) 64 = kv.2
      rw [m₆, o₆ _ (by decide)]; exact hm₄ kv hkv
    · rw [o₆ r h3, o₄ r h1 h2, o₃ r h1 h2, o₂ r h2]
  refine WP.seq (WP.mono (keyLoop_wp (e₀ := 2) (N := 8 * g - 2) (wk := fun k => 8 * g - 1 - k)
    (f := fun x => x - BitVec.ofNat 64 8) (fun s => subI_ok s .a0 .a0 8 (by decide)) (by omega_arith)
    (fun k hk => by omega_arith) (fun k hk => ?_) (fun k hk => ?_) (by omega_arith) hinv) fun s h => ?_)
  · have := sub8 sched (w := 8 * g - 1 - (k + 1))
    rwa [show 8 * g - 1 - (k + 1) + 1 = 8 * g - 1 - k by omega_arith] at this
  · simp only [F, Camellia.decPerm, show ¬ 2 + k < 2 by omega_arith, show 2 + k < 8 * g by omega_arith, ↓reduceIte,
      show 8 * g + 1 - (2 + k) = 8 * g - 1 - k by omega_arith]
  -- `kw1`, `kw2` to entries `8 g` and `8 g + 1`.
  have hk₇ := h.pre
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := subI_ok s .a0 .a0 8 (by decide)
  have hr3₇ : s₇.gpr .a0 = sched + BitVec.ofNat 64 (8 * 0) := by
    rw [r₇, h.a0, show 8 * g - 1 - (8 * g - 2) = 0 + 1 by omega_arith, sub8]
  have hk₇' : KeyPre s₇ b sched := hk₇.congr (o₇ _ (by decide)) rd₇ wr₇
  have hm₇ : MasksOk s₇ := fun kv hkv => by
    show s₇.mem.readW (wordAddr (s₇.gpr sb) kv.1) 64 = kv.2
    rw [m₇, o₇ _ (by decide)]; exact h.masks kv hkv
  have hkp₇ : s₇.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (8 * g)) := by
    rw [o₇ _ (by decide), h.kpos, show 2 + (8 * g - 2) = 8 * g by omega_arith]
  obtain ⟨s₈, e₈, hk₈, kp₈, o₈, -, rd₈, wr₈, hm₈, hf₈, E₈, P₈⟩ :=
    keyOne_inv (s₀ := s₀) (d := 0) (Or.inl rfl) hk₇' hkp₇ (by omega_arith) hr3₇ (by omega_arith) hm₇
      (by rw [m₇]; exact h.frame)
  obtain ⟨s₉, e₉, hk₉, -, o₉, -, rd₉, wr₉, hm₉, hf₉, E₉, P₉⟩ :=
    keyOne_inv (s₀ := s₀) (d := 8) (Or.inr rfl) hk₈ kp₈ (by omega_arith) (by rw [o₈ _ (by decide) (by decide), hr3₇])
      (by omega_arith) hm₈ hf₈
  refine WP.of_runBlock ⟨s₉, by
    rw [runBlock_append', runBlock_append', e₇, Option.bind_some, e₈, Option.bind_some, e₉],
    ⟨hk₉, fun i hi => ?_, hm₉, hf₉, fun r h1 h2 h3 _ => ?_, by rw [rd₉, rd₈, rd₇, h.rd],
    by rw [wr₉, wr₈, wr₇, h.wr]⟩, ?_⟩
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
  · rw [o₉ r h1 h2, o₈ r h1 h2, o₇ r h3, h.regs r h1 h2 h3]
  · rw [o₉ _ (by decide) (by decide), o₈ _ (by decide) (by decide), o₇ _ (by decide),
      h.regs _ (by decide) (by decide) (by decide)]

end VG.Proof.Camellia.RISCV64

end

end

/-! ### `Camellia.RISCV64.Copy`, which only this module used -/

section

/-!
# Copying blocks on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/Copy.lean`): the loops `copyInBlocks`
and `copyOutBlocks` copy `c ≥ 1` blocks of 16 bytes from `t3` to `t4`
(areas that do not overlap), through `t0`–`t2`, counting down `t5`, and
change nothing else in memory. `copyLoop_wp` proves the loop once for any
copy of a word (`CopiesWord`): `copyIn_word` reads the data a byte at a
time and writes the aligned tail buffer, `copyOut_word` the reverse.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (t0 t1 t2)

/-- What copying a word at offset `d` does: `[t4 + d] := [t3 + d]`,
through `t0`–`t2`, for the pointers at block `j < c` from `A` and `B`. -/
def CopiesWord (W : Nat → List Instr) (A B : Addr) (c : Nat) : Prop :=
  ∀ (s : State) (j d : Nat), j < c → (d = 0 ∨ d = 8) →
    s.gpr .t3 = A + BitVec.ofNat 64 (16 * j) → s.gpr .t4 = B + BitVec.ofNat 64 (16 * j) →
    InRegions (s.rd ++ s.wr) (s.gpr .t3 + BitVec.ofNat 64 d) 8 →
    InRegions s.wr (s.gpr .t4 + BitVec.ofNat 64 d) 8 →
    ∃ s', runBlock isa (W d) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .t4 + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .t3 + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

/-- A word of the data to the tail buffer. -/
def wordIn (d : Nat) : List Instr :=
  Impl.Words64.RISCV64.loadLE64 t0 t1 t2 .t3 d ++ [.store .d t0 .t4 d]

/-- A word of the tail buffer to the data. -/
def wordOut (d : Nat) : List Instr :=
  [.load .d t0 .t3 d] ++ Impl.Words64.RISCV64.storeLE64 t0 t1 t2 .t4 d

theorem copyInBlocks_eq : copyInBlocks = .loop (.block (wordIn 0 ++ (wordIn 8 ++ copyStep))) (.nonzero .t5) := by
  simp only [copyInBlocks, wordIn, List.append_assoc]

theorem copyOutBlocks_eq :
    copyOutBlocks = .loop (.block (wordOut 0 ++ (wordOut 8 ++ copyStep))) (.nonzero .t5) := by
  simp only [copyOutBlocks, wordOut, List.append_assoc]

theorem copyIn_word {A B : Addr} {c : Nat} (hB : B.toNat % 8 = 0) : CopiesWord wordIn A B c := by
  intro s j d _ hd _ hdst hr hw
  obtain ⟨s₁, e₁, u₁⟩ := WP.runBlock_of (Words64.loadLE64_ok (s := s) (d := t0) (tmp := t1) (tmp2 := t2)
    (n := .t3) (off := d) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rcases hd with rfl | rfl <;> decide) hr)
  obtain h4 : s₁.gpr .t4 = s.gpr .t4 := u₁.other _ (by decide) (by decide) (by decide)
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .t4 + BitVec.ofNat 64 d) (s₁.gpr t0) }, ?_, ?_,
    fun r h0 h1 h2 => u₁.other r h0 h1 h2, u₁.rd, u₁.wr⟩
  · rw [wordIn, runBlock_append', e₁, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_store_d (show d < 2048 by omega_using [hd])
      (by rw [h4, hdst, addr_add]; exact Spill.al8 hB (by omega_using [hd]))
      (by rw [u₁.wr, h4]; exact hw)]
  · show s₁.mem.writeW _ _ = _
    rw [u₁.mem, h4, u₁.gpr]

theorem copyOut_word {A B : Addr} {c : Nat} (hA : A.toNat % 8 = 0) : CopiesWord wordOut A B c := by
  intro s j d _ hd hsrc _ hr hw
  let s₁ := s.write t0 (s.mem.readW (s.gpr .t3 + BitVec.ofNat 64 d) 64)
  obtain e₁ : runBlock isa [.load .d t0 .t3 d] s = some s₁ := by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_load_d (show d < 2048 by omega_using [hd])
      (by rw [hsrc, addr_add]; exact Spill.al8 hA (by omega_using [hd])) hr]
    rfl
  obtain h4 : s₁.gpr .t4 = s.gpr .t4 := RegUpd.gpr_write_of_ne _ _ (by decide)
  obtain ⟨s₂, e₂, g₂, m₂, rd₂, wr₂, -⟩ := WP.runBlock_of (Words64.storeLE64_ok (s := s₁) (v := t0)
    (tmp := t1) (tmp2 := t2) (n := .t4) (off := d) (by decide) (by decide) (by decide) (by decide)
    (by rcases hd with rfl | rfl <;> decide) (by rw [h4]; exact hw))
  refine ⟨s₂, ?_, ?_, fun r h0 h1 h2 => by rw [g₂ r h1 h2]; exact RegUpd.gpr_write_of_ne _ _ h0, rd₂, wr₂⟩
  · rw [wordOut, runBlock_append', e₁, Option.bind_some]; exact e₂
  · rw [m₂, h4, RegUpd.gpr_write_self]; rfl

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .t3 = A + BitVec.ofNat 64 (16 * j)
  dst : s.gpr .t4 = B + BitVec.ofNat 64 (16 * j)
  cnt : s.gpr .t5 = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ t0 → r ≠ t1 → r ≠ t2 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyLoop_wp {W : Nat → List Instr} {A B : Addr} {c : Nat} {s₀ : State} (hW : CopiesWord W A B c) (hc : 0 < c) (hcBound : c ≤ 17)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa (.loop (.block (W 0 ++ (W 8 ++ copyStep))) (.nonzero .t5)) s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_arith, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  obtain hA0 := hA (2 * j) (by omega_arith)
  obtain hA1 := hA (2 * j + 1) (by omega_arith)
  obtain hB0 := hB (2 * j) (by omega_arith)
  obtain hB1 := hB (2 * j + 1) (by omega_arith)
  have hfA : Frame [⟨B, 16 * c⟩] s₀.mem s.mem := hi.frame
  obtain hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hfA.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega_arith) ht
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := hW s j 0 hj (Or.inl rfl) hi.src hi.dst
    (by rw [hi.rd, hi.wr, hi.src, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hA0)
    (by rw [hi.wr, hi.dst, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega_arith]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := hW s₁ j 8 hj (Or.inr rfl)
    (by rw [g₁ _ (by decide) (by decide) (by decide), hi.src])
    (by rw [g₁ _ (by decide) (by decide) (by decide), hi.dst])
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide) (by decide) (by decide), hi.src, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hA1)
    (by rw [wr₁, hi.wr, g₁ _ (by decide) (by decide) (by decide), hi.dst, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega_arith]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ .t3 .t3 16 (by decide)
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addI_ok s₃ .t4 .t4 16 (by decide)
  obtain ⟨s₅, e₅, c₅, o₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ .t5 .t5 1 (by decide)
  refine WP.of_runBlock ⟨s₅, by
    rw [show copyStep = [.addi .t3 .t3 16] ++ ([.addi .t4 .t4 16] ++ [.addi .t5 .t5 (-1)]) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some, runBlock_append', e₃,
      Option.bind_some, runBlock_append', e₄, Option.bind_some]
    exact e₅, ?_⟩
  obtain hn : 16 * c < 2 ^ 64 := by omega_arith
  obtain r1 : s₁.gpr .t4 = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide) (by decide) (by decide), hi.dst]
  obtain a1 : s₁.gpr .t3 = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide) (by decide) (by decide), hi.src]
  obtain hm : s₅.mem = (s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64)) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  obtain hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.dst, hi.src, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area.
  obtain hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega_arith) hn)]
  obtain hc₅ : s₅.gpr .t5 = BitVec.ofNat 64 (c - (j + 1)) := by
    rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide), hi.cnt,
      VG.Offset.ofNat_sub_ofNat (by omega_arith), show c - j - 1 = c - (j + 1) by omega_arith]
  obtain hinv : CopyInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, hc₅, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 h5 h6 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide) (by decide) (by decide), a1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide) (by decide) (by decide), r1, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega_arith]
    · rw [hm, writeW_readW_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega_arith)]; omega_arith), off_sub_toNat B h8 (by omega_arith), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega_arith, hA₁ t (by omega_arith), hAs t (by omega_arith)]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega_arith)]; omega_arith), off_sub_toNat B h0 (by omega_arith), addr_add,
            show 16 * j + (t - 16 * j) = t by omega_arith, hAs t (by omega_arith)]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))]
          exact hi.copied t (by omega_arith)
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega_arith))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega_arith)), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega_arith))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4 h5 h6, g₁ r h4 h5 h6, hi.regs r h1 h2 h3 h4 h5 h6]
  obtain hz : (s₅.gpr .t5 == 0) = decide (c - (j + 1) = 0) := by
    rw [hc₅, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, Bool.eq_iff_iff, beq_iff_eq,
      decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega_arith
    · intro h; rw [h]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_nonzero s₅ .t5).trans (by rw [hz]; simp; omega_arith),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_nonzero s₅ .t5).trans (by rw [hz]; simp; omega_arith), c - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hinv⟩

theorem copyInBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hB8 : B.toNat % 8 = 0) (hc : 0 < c) (hc8 : c ≤ 8)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyInBlocks s₀ (CopyInv A B c s₀ c) := by
  rw [copyInBlocks_eq]; exact copyLoop_wp (copyIn_word hB8) hc (by omega_using [hc8]) hA hB hsep hs

theorem copyOutBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hA8 : A.toNat % 8 = 0) (hc : 0 < c) (hc8 : c ≤ 8)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyOutBlocks s₀ (CopyInv A B c s₀ c) := by
  rw [copyOutBlocks_eq]; exact copyLoop_wp (copyOut_word hA8) hc (by omega_using [hc8]) hA hB hsep hs

end VG.Proof.Camellia.RISCV64

end

end


/-!
# A group of blocks of Camellia ECB on RISC-V

As on RISCV64 (`Proof/Camellia/RISCV64/Group.lean`). `dataGroup_wp`: one iteration of the data loop copies the group's blocks
(eight, or the last one to seven) to the tail buffer, transforms it
(`crypt8_ok`, which keeps the data pointer, the blocks left and the
postwhitening's address in `a2`–`a4`), copies the blocks back and steps to
the next group.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 t2 kp movR ldS stS shrI)
open VG.Proof.Aes.RISCV64 (sboxWrites)

/-! ## Small blocks -/

/-- `mv d, n`. -/
theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  let ⟨s', e, h1, h2, h3, h4, h5⟩ := addI_ok s d n 0 (by decide)
  ⟨s', e, by rw [h1]; exact BitVec.add_zero _, h2, h3, h4, h5⟩

/-- `li d, v`, with `v` a literal. -/
theorem liN_ok (s : State) (d : Reg) (v : Nat) (hv : v < 2048) :
    ∃ s', runBlock isa [.li d (OfNat.ofNat v)] s = some s' ∧ s'.gpr d = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  li_ok s d hv

/-- `addi d, n, imm`, with `imm` a `Nat` cast. -/
theorem addIc_ok (s : State) (d n : Reg) (imm : Nat) (h : imm < 2048) :
    ∃ s', runBlock isa [.addi d n (imm : Int)] s = some s' ∧ s'.gpr d = s.gpr n + BitVec.ofNat 64 imm ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  addI_ok s d n imm h

theorem lsr3_beq {v : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v >>> 3 == 0) = decide (v < 8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow] at this
    simp at this
    omega_arith
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.shiftRight_eq_div_pow]
    simp
    omega_arith

/-- `r12 := min(r6, 8)`. -/
theorem groupCount_wp {s : State} {v : Nat} (hr : s.gpr .a3 = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa groupCount s fun s' => s'.gpr .t6 = BitVec.ofNat 64 (min v 8) ∧
      (∀ r, r ≠ .t6 → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write t0 (s.gpr .a3 >>> 3)
  obtain e₁ : runBlock isa [shrI t0 .a3 3] s = some s₁ := by
    simp only [shrI, runBlock_cons, runStep_some, runBlock_nil, exec_shift_d (show 3 < 64 by decide)]; rfl
  obtain t₁ : s₁.gpr t0 = BitVec.ofNat 64 v >>> 3 := by
    rw [RegUpd.gpr_write_self, hr]
  obtain o₁ : ∀ r, r ≠ t0 → s₁.gpr r = s.gpr r := fun r hr => RegUpd.gpr_write_of_ne _ _ hr
  unfold groupCount
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.ite (decide (8 ≤ v)) ((eval_nonzero s₁ t0).trans (by rw [t₁, lsr3_beq hv]; by_cases h : v < 8 <;> simp [h] <;> omega_arith))
    (fun h => ?_) (fun h => ?_)
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := liN_ok s₁ .t6 8 (by decide)
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, Nat.min_eq_right (by simp at h; omega_arith)]
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ .t6 .a3
    refine WP.of_runBlock ⟨s₂, e₂, ?_, fun r h1 h2 => by rw [o₂ r h1, o₁ r h2], m₂, rd₂, wr₂⟩
    rw [r₂, o₁ _ (by decide), hr, Nat.min_eq_left (by simp at h; omega_arith)]

/-- `tailAddr r`. -/
theorem tailAddr_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa (tailAddr r) s = some s' ∧ s'.gpr r = s.gpr sb + BitVec.ofNat 64 (8 * tailSlot) ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  addIc_ok s r sb (8 * tailSlot) (by decide)

/-! ## The scratch buffer's contents -/

/-- The masks, in the memory at `b`. -/
def MasksAt (m : Mem) (b : Addr) : Prop := ∀ kv ∈ allMasks, m.readW (wordAddr b kv.1) 64 = kv.2

theorem MasksOk.at {s : State} {b : Addr} (h : MasksOk s) (hb : s.gpr sb = b) : MasksAt s.mem b :=
  fun kv hkv => by rw [← hb]; exact h kv hkv

theorem MasksAt.ok {s : State} {b : Addr} (h : MasksAt s.mem b) (hb : s.gpr sb = b) : MasksOk s :=
  fun kv hkv => by show s.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = kv.2; rw [hb]; exact h kv hkv

/-- What the data loop keeps in the scratch buffer: the masks, the table and
the saved registers. -/
structure ScrOk (s₀ : State) (b : Addr) (g : Nat) (E : Nat → BitVec 64) (m : Mem) : Prop where
  masks : MasksAt m b
  keys : ∀ i < 8 * g + 2, EntryOk m b i (E i)
  saved : Saved s₀ b m

/-- The slots `ScrOk` reads: 48–58, 128–399 and 80–91. -/
abbrev scrRegions (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 (8 * 48), 88⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot), 8 * 272⟩,
    ⟨b + BitVec.ofNat 64 (8 * savedSlot), 96⟩]

theorem allMasks_range : ∀ kv ∈ allMasks, 48 ≤ kv.1 ∧ kv.1 < 59 := by decide

theorem ScrOk.frame {s₀ : State} {b : Addr} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g ≤ 4) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ t ∈ scrRegions b, ∀ r ∈ rs, Region.Disjoint t r) :
    ScrOk s₀ b g E m' := by
  obtain hR : ∀ t ∈ scrRegions b, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨fun kv hkv => ?_, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · have hk := allMasks_range kv hkv
    rw [← h.masks kv hkv]
    exact hR _ List.mem_cons_self (8 * kv.1) (VG.Offset.sub b (by omega_arith) (by omega_arith))
  · exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * keySlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_arith) (by rw [keySlot_eq]; omega_arith))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_arith) (by omega_arith))

theorem ScrOk.frame2 {s₀ : State} {b : Addr} {g : Nat} {E : Nat → BitVec 64} {m m' : Mem}
    (h : ScrOk s₀ b g E m) (hg : g ≤ 4) {rs : List Region} (hf : Frame rs m m') (hm : MasksAt m' b)
    (hd : ∀ t ∈ (scrRegions b).tail, ∀ r ∈ rs, Region.Disjoint t r) : ScrOk s₀ b g E m' := by
  obtain hR : ∀ t ∈ (scrRegions b).tail, ∀ d, Region.Sub ⟨b + BitVec.ofNat 64 d, 8⟩ t →
      m'.readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 := fun t ht d hs =>
    hf.readW (Region.contains_self _ _) (fun r hr => (hd _ ht r hr).sub_left hs) (by decide)
  refine ⟨hm, fun i hi => (h.keys i hi).congr fun j hj => ?_, fun i hi => ?_⟩
  · exact hR _ List.mem_cons_self (8 * keySlot + 64 * i + 8 * j)
      (VG.Offset.sub b (by omega_arith) (by rw [keySlot_eq]; omega_arith))
  · rw [← h.saved i hi]
    exact hR _ (List.mem_cons_of_mem _ List.mem_cons_self) (8 * (savedSlot + i))
      (VG.Offset.sub b (by omega_arith) (by omega_arith))

/-! ## The data loop -/

/-- The scratch buffer at `b` and the `n` blocks at `D`. -/
structure GPre (s₀ : State) (b D : Addr) (n g : Nat) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitD : D.toNat + 16 * n ≤ 2 ^ 64
  hg : g = 3 ∨ g = 4
  al : b.toNat % 8 = 0

/-- What a copy of `c` blocks from `X` to `Y` leaves. -/
def CopyPost (s : State) (X Y : Addr) (c : Nat) (s' : State) : Prop :=
  (∀ t < 16 * c, s'.mem (Y + BitVec.ofNat 64 t) = s.mem (X + BitVec.ofNat 64 t)) ∧
    Frame [⟨Y, 16 * c⟩] s.mem s'.mem ∧
    (∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ t0 → r ≠ t1 → r ≠ t2 → s'.gpr r = s.gpr r) ∧
    s'.rd = s.rd ∧ s'.wr = s.wr

/-- `copyInBlocks` from `t3` to `t4` (aligned), `t5` blocks, set up. -/
theorem copyIn_wp {s : State} {X Y : Addr} {c : Nat} (hY8 : Y.toNat % 8 = 0) (hc : 0 < c) (hc8 : c ≤ 8)
    (hx : s.gpr .t3 = X) (hy : s.gpr .t4 = Y) (hcx : s.gpr .t5 = BitVec.ofNat 64 c)
    (hX : ∀ t < 2 * c, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hY : ∀ t < 2 * c, InRegions s.wr (Y + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa copyInBlocks s (CopyPost s X Y c) :=
  WP.mono (copyInBlocks_wp hY8 hc hc8 hX hY hsep ⟨by rw [hx]; simp, by rw [hy]; simp,
    by rw [hcx, Nat.sub_zero], fun t ht => by omega_arith, Frame.refl _ _, fun _ _ _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s' h => ⟨h.copied, h.frame, h.regs, h.rd, h.wr⟩

/-- `copyOutBlocks` from `t3` (aligned) to `t4`, `t5` blocks, set up. -/
theorem copyOut_wp {s : State} {X Y : Addr} {c : Nat} (hX8 : X.toNat % 8 = 0) (hc : 0 < c) (hc8 : c ≤ 8)
    (hx : s.gpr .t3 = X) (hy : s.gpr .t4 = Y) (hcx : s.gpr .t5 = BitVec.ofNat 64 c)
    (hX : ∀ t < 2 * c, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (8 * t)) 8)
    (hY : ∀ t < 2 * c, InRegions s.wr (Y + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨X, 16 * c⟩ ⟨Y, 16 * c⟩) :
    WP isa copyOutBlocks s (CopyPost s X Y c) :=
  WP.mono (copyOutBlocks_wp hX8 hc hc8 hX hY hsep ⟨by rw [hx]; simp, by rw [hy]; simp,
    by rw [hcx, Nat.sub_zero], fun t ht => by omega_arith, Frame.refl _ _, fun _ _ _ _ _ _ _ => rfl, rfl, rfl⟩)
    fun s' h => ⟨h.copied, h.frame, h.regs, h.rd, h.wr⟩

/-- The data loop, before group `k`. -/
structure GInv (s₀ : State) (b D : Addr) (n g : Nat) (E : Nat → BitVec 64) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  a2 : s.gpr .a2 = D + BitVec.ofNat 64 (128 * k)
  a3 : s.gpr .a3 = BitVec.ofNat 64 (n - 8 * k)
  lt : 8 * k < n
  a4 : s.gpr .a4 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g)
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem D n (8 * k) (outF s₀.mem D g E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The data loop, done. -/
structure GDone (s₀ : State) (b D : Addr) (n g : Nat) (E : Nat → BitVec 64) (s : State) : Prop where
  base : s.gpr sb = b
  scr : ScrOk s₀ b g E s.mem
  data : DInv s₀.mem s.mem D n n (outF s₀.mem D g E)
  frame : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem dataGroup_wp {s₀ : State} {b D : Addr} {n g : Nat} {E : Nat → BitVec 64} (hp : GPre s₀ b D n g)
    {k : Nat} {s : State} (hi : GInv s₀ b D n g E k s) :
    WP isa Impl.Camellia.RISCV64.group s fun s' => (s'.gpr .a3 = 0 ∧ GDone s₀ b D n g E s') ∨
      (s'.gpr .a3 ≠ 0 ∧ GInv s₀ b D n g E (k + 1) s') := by
  have hfit := hp.fit
  have hfitD := hp.fitD
  have hk := hi.lt
  obtain hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega_arith
  rw [slots_eq] at hfit
  let v := n - 8 * k
  let c := min v 8
  obtain hv : v < 2 ^ 64 := by omega_arith
  obtain hc0 : 0 < c := by omega_arith
  obtain hc8 : c ≤ 8 := by omega_arith
  obtain hkc : 128 * k + 16 * c ≤ 16 * n := by omega_arith
  let A := D + BitVec.ofNat 64 (128 * k)
  let T := b + BitVec.ofNat 64 (8 * tailSlot)
  obtain hT8 : T.toNat % 8 = 0 := Spill.al8 hp.al (by decide)
  obtain hwS : (⟨b, 8 * slots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr
  obtain hwD : (⟨D, 16 * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  obtain inT : ∀ t, t < 16 → InRegions s.wr (T + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwS, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, tailSlot_eq]; omega_arith) (by rw [tailSlot_eq]; omega_arith)
  obtain inA : ∀ t, t < 2 * c → InRegions s.wr (A + BitVec.ofNat 64 (8 * t)) 8 := by
    intro t ht
    refine ⟨_, hwD, ?_⟩
    rw [addr_add]
    exact VG.Offset.contains_base D (by omega_arith) (by omega_arith)
  obtain sepAT : Region.Disjoint ⟨A, 16 * c⟩ ⟨T, 16 * c⟩ :=
    (hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq, tailSlot_eq]; omega_arith))
  unfold Impl.Camellia.RISCV64.group copyIn
  -- The group's blocks to the tail buffer.
  refine WP.seq (WP.seq (WP.mono (groupCount_wp hi.a3 hv) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_))
  obtain ⟨s₂a, e₂a, r₂a, o₂a, m₂a, rd₂a, wr₂a⟩ := movR_ok s₁ .t3 .a2
  obtain ⟨s₂b, e₂b, r₂b, o₂b, m₂b, rd₂b, wr₂b⟩ := tailAddr_ok s₂a .t4
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₂b .t5 .t6
  obtain rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₂b, rd₂a, rd₁]
  obtain wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₂b, wr₂a, wr₁]
  obtain mem₂ : s₂.mem = s.mem := by rw [m₂, m₂b, m₂a, m₁]
  obtain g₂ : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ .t6 → r ≠ t0 → s₂.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₂ r h3, o₂b r h2, o₂a r h1, o₁ r h4 h5]
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    rw [runBlock_append', runBlock_append', e₂a, Option.bind_some, e₂b, Option.bind_some, e₂], ?_⟩)
  refine WP.mono (copyIn_wp (X := A) (Y := T) hT8 hc0 hc8
    (by rw [o₂ _ (by decide), o₂b _ (by decide), r₂a, o₁ _ (by decide) (by decide), hi.a2])
    (by rw [o₂ _ (by decide), r₂b, o₂a _ (by decide), o₁ _ (by decide) (by decide), hi.base])
    (by rw [r₂, o₂b _ (by decide), o₂a _ (by decide), c₁])
    (fun t ht => by rw [rd₂', wr₂']; exact inRd (inA t ht))
    (fun t ht => by rw [wr₂']; exact inT t (by omega_arith)) sepAT) fun s₃ ⟨cp₃, f₃, g₃, rd₃, wr₃⟩ => ?_
  obtain f₃' : Frame [⟨T, 16 * c⟩] s.mem s₃.mem := by rw [← mem₂]; exact f₃
  obtain wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂']
  obtain rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂']
  obtain g₃' : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ .t6 → r ≠ t0 → r ≠ t1 → r ≠ t2 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [g₃ r h1 h2 h3 h5 h6 h7, g₂ r h1 h2 h3 h4 h5]
  obtain base₃ : s₃.gpr sb = b := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.base]
  obtain sc₃ : ScrOk s₀ b g E s₃.mem := by
    refine hi.scr.frame hg4 (mem₂ ▸ f₃) fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine VG.Offset.disjoint b ?_ ?_ ?_ <;>
      (try simp only [tailSlot_eq, keySlot_eq, savedSlot_eq]) <;> omega_arith
  -- The eight blocks.
  obtain hcore : CorePre s₃ g E :=
    { scr := by rw [base₃, wr₃']; exact hwS
      fit := by rw [base₃, slots_eq]; exact hfit
      hg := hp.hg
      nk34 := by rcases hp.hg with h | h <;> omega_arith
      al := by rw [base₃]; exact hp.al
      masks := sc₃.masks.ok base₃
      bound := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.a4, base₃]
      keys := fun i hi' => by rw [base₃]; exact sc₃.keys i hi' }
  refine WP.seq (WP.mono (crypt8_ok hcore) fun s₅ ⟨c₅, b₅⟩ => ?_)
  obtain base₅ : s₅.gpr sb = b := by rw [c₅.base, base₃]
  obtain f₅ : Frame [⟨b, 8 * savedSlot⟩, ⟨T, 128⟩] s₃.mem s₅.mem := by
    have := c₅.frame; rw [ctxRegions, base₃] at this; exact this
  have hT : T = b + BitVec.ofNat 64 (8 * tailSlot) := rfl
  obtain sc₅ : ScrOk s₀ b g E s₅.mem := by
    refine sc₃.frame2 hg4 f₅ (c₅.masks.at base₅) fun t ht r hr => ?_
    simp only [scrRegions, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at ht hr
    rcases ht with rfl | rfl <;> rcases hr with rfl | rfl
    · exact VG.Offset.disjoint_base b (by decide) (by decide)
    · rw [hT]; exact VG.Offset.disjoint b (by decide) (by decide) (by decide)
    · exact VG.Offset.disjoint_base b (by decide) (by decide)
    · rw [hT]; exact VG.Offset.disjoint b (by decide) (by decide) (by decide)
  obtain k₅ : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → s₅.gpr r = s₃.gpr r := fun r h1 h2 h3 => c₅.keep r h1 h2 h3
  obtain a2₅ : s₅.gpr .a2 = A := by
    rw [k₅ _ (by decide) (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hi.a2]
  obtain a3₅ : s₅.gpr .a3 = BitVec.ofNat 64 v := by
    rw [k₅ _ (by decide) (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hi.a3]
  obtain a4₅ : s₅.gpr .a4 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [k₅ _ (by decide) (by decide) (by decide), g₃' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hi.a4]
  obtain wr₅' : s₅.wr = s.wr := by rw [c₅.wr, wr₃']
  obtain rd₅' : s₅.rd = s.rd := by rw [c₅.rd, rd₃']
  -- The tail buffer back to the group's blocks.
  unfold copyOut
  refine WP.seq (WP.seq (WP.mono (groupCount_wp a3₅ hv) fun s₇ ⟨c₇, o₇, m₇, rd₇, wr₇⟩ => ?_))
  obtain ⟨s₈a, e₈a, r₈a, o₈a, m₈a, rd₈a, wr₈a⟩ := tailAddr_ok s₇ .t3
  obtain ⟨s₈b, e₈b, r₈b, o₈b, m₈b, rd₈b, wr₈b⟩ := movR_ok s₈a .t4 .a2
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := movR_ok s₈b .t5 .t6
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [runBlock_append', e₈a, Option.bind_some,
      show ([movR .t4 .a2, movR .t5 .t6] : List Instr) = [movR .t4 .a2] ++ [movR .t5 .t6] from rfl,
      runBlock_append', e₈b, Option.bind_some, e₈], ?_⟩)
  obtain mem₈ : s₈.mem = s₅.mem := by rw [m₈, m₈b, m₈a, m₇]
  obtain wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₈b, wr₈a, wr₇, wr₅']
  obtain rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₈b, rd₈a, rd₇, rd₅']
  obtain g₈ : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ .t6 → r ≠ t0 → s₈.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [o₈ r h3, o₈b r h2, o₈a r h1, o₇ r h4 h5]
  refine WP.mono (copyOut_wp (X := T) (Y := A) hT8 hc0 hc8
    (by rw [o₈ _ (by decide), o₈b _ (by decide), r₈a, o₇ _ (by decide) (by decide), base₅])
    (by rw [o₈ _ (by decide), r₈b, o₈a _ (by decide), o₇ _ (by decide) (by decide), a2₅])
    (by rw [r₈, o₈b _ (by decide), o₈a _ (by decide), c₇])
    (fun t ht => by rw [rd₈', wr₈']; exact inRd (inT t (by omega_arith)))
    (fun t ht => by rw [wr₈']; exact inA t ht) sepAT.symm) fun s₉ ⟨cp₉, f₉, g₉, rd₉, wr₉⟩ => ?_
  obtain g₉' : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → r ≠ .t6 → r ≠ t0 → r ≠ t1 → r ≠ t2 → s₉.gpr r = s₅.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [g₉ r h1 h2 h3 h5 h6 h7, g₈ r h1 h2 h3 h4 h5]
  obtain t6₉ : s₉.gpr .t6 = BitVec.ofNat 64 c := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), o₈ _ (by decide), o₈b _ (by decide),
      o₈a _ (by decide), c₇]
  obtain base₉ : s₉.gpr sb = b := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), base₅]
  obtain a2₉ : s₉.gpr .a2 = A := by rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a2₅]
  obtain a3₉ : s₉.gpr .a3 = BitVec.ofNat 64 v := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a3₅]
  obtain a4₉ : s₉.gpr .a4 = b + BitVec.ofNat 64 (8 * keySlot + 512 * g) := by
    rw [g₉' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), a4₅]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈', hi.wr]
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈', hi.rd]
  -- The scratch buffer and the frame.
  obtain subS : ∀ {d l : Nat}, d + l ≤ 8 * slots → Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨b, 8 * slots⟩ :=
    fun h => VG.Offset.sub_base b h
  obtain sc₉ : ScrOk s₀ b g E s₉.mem := by
    refine (mem₈ ▸ sc₅).frame hg4 f₉ fun t ht r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    obtain hsub : Region.Sub t ⟨b, 8 * slots⟩ := by
      simp only [scrRegions, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> refine subS ?_ <;> (try simp only [keySlot_eq, savedSlot_eq]) <;>
        rw [slots_eq] <;> omega_arith
    exact ((hp.sep.sub_left (VG.Offset.sub_base D (by omega_arith))).sub_right hsub).symm
  obtain fr₉ : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s.mem s₉.mem := by
    refine (((mem₂ ▸ f₃).sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((f₅.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      ((mem₈ ▸ f₉).sub fun r hr => ⟨⟨D, 16 * n⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)))
    · simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by decide)
      · exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base D (by omega_arith)
  -- The blocks the eight-block code read are the group's, as on entry.
  obtain hblk : ∀ j < c, blk s₃ j = Spec.Camellia.blockAt s₀.mem (D + BitVec.ofNat 64 (16 * (8 * k + j))) := by
    intro j hj
    apply Vector.ext; intro u hu
    simp only [blk, Spec.Camellia.blockAt, Vector.getElem_ofFn]
    rw [base₃, addr_add]
    obtain ht : 16 * j + u < 16 * c := by omega_arith
    have := cp₃ (16 * j + u) ht
    rw [addr_add, show 8 * tailSlot + (16 * j + u) = 8 * tailSlot + 16 * j + u by omega_arith] at this
    rw [this, mem₂, addr_add, hi.data _ (by omega_arith), ite_eq_right (by omega_arith),
      show 128 * k + (16 * j + u) = 16 * (8 * k + j) + u by omega_arith, addr_add]
  obtain hdata : DInv s₀.mem s₉.mem D n (8 * k + c) (outF s₀.mem D g E) := by
    intro i hin
    by_cases hin1 : 128 * k ≤ i ∧ i < 128 * k + 16 * c
    · have e1 : D + BitVec.ofNat 64 i = A + BitVec.ofNat 64 (i - 128 * k) := by
        rw [addr_add, show 128 * k + (i - 128 * k) = i by omega_arith]
      rw [e1, cp₉ _ (by omega_arith), mem₈, ite_eq_left (show i < 16 * (8 * k + c) by omega_arith),
        show i / 16 = 8 * k + (i - 128 * k) / 16 by omega_arith, show i % 16 = (i - 128 * k) % 16 by omega_arith]
      obtain hj : (i - 128 * k) / 16 < c := by omega_arith
      obtain eT : T + BitVec.ofNat 64 (i - 128 * k) = s₅.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * ((i - 128 * k) / 16)) +
          BitVec.ofNat 64 ((i - 128 * k) % 16) := by
        rw [base₅, addr_add, addr_add, show 8 * tailSlot + 16 * ((i - 128 * k) / 16) + (i - 128 * k) % 16 =
          8 * tailSlot + (i - 128 * k) by omega_arith]
      rw [eT, ← blockAt_getD s₅.mem _ (Nat.mod_lt _ (by decide))]
      show (blk s₅ _).getD _ 0 = _
      rw [b₅ _ (by omega_arith), hblk _ hj]
      rfl
    · have hout : ∀ r ∈ [(⟨A, 16 * c⟩ : Region)], ¬ r.Contains (D + BitVec.ofNat 64 i) 1 := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact not_contains_off D (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      obtain hdS : ∀ {rs : List Region}, (∀ r ∈ rs, Region.Sub r ⟨b, 8 * slots⟩) →
          ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r := fun h r hr => hp.sep.sub_right (h r hr)
      rw [f₉ _ hout, mem₈,
        f₅.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Region.sub_prefix (by decide)
          · exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith)) (by simp only; omega_arith) hin,
        f₃'.bytes (R := ⟨D, 16 * n⟩) (hdS fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact subS (by rw [slots_eq, tailSlot_eq]; omega_arith))
          (by simp only; omega_arith) hin,
        hi.data i hin]
      by_cases h2 : i < 128 * k
      · rw [ite_eq_left (show i < 16 * (8 * k) by omega_arith), ite_eq_left (show i < 16 * (8 * k + c) by omega_arith)]
      · rw [ite_eq_right (show ¬ i < 16 * (8 * k) by omega_arith), ite_eq_right (show ¬ i < 16 * (8 * k + c) by omega_arith)]
  obtain fr : Frame [⟨b, 8 * slots⟩, ⟨D, 16 * n⟩] s₀.mem s₉.mem := hi.frame.trans fr₉
  -- On to the next group.
  obtain ⟨s₁₀, e₁₀, r₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := subR_ok s₉ .a3 .a3 .t6
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addI_ok s₁₀ .a2 .a2 128 (by decide)
  refine WP.of_runBlock ⟨s₁₁, by
    rw [show ([Instr.sub .a3 .a3 .t6, .addi .a2 .a2 128] : List Instr) =
      [.sub .a3 .a3 .t6] ++ [.addi .a2 .a2 128] from rfl, runBlock_append', e₁₀,
      Option.bind_some, e₁₁], ?_⟩
  obtain hm : s₁₁.mem = s₉.mem := by rw [m₁₁, m₁₀]
  obtain a3₁₁ : s₁₁.gpr .a3 = BitVec.ofNat 64 (v - c) := by
    rw [o₁₁ _ (by decide), r₁₀, a3₉, t6₉, VG.Offset.ofNat_sub_ofNat (by omega_arith)]
  obtain base₁₁ : s₁₁.gpr sb = b := by rw [o₁₁ _ (by decide), o₁₀ _ (by decide), base₉]
  obtain rd₁₁' : s₁₁.rd = s₀.rd := by rw [rd₁₁, rd₁₀, rd₉']
  obtain wr₁₁' : s₁₁.wr = s₀.wr := by rw [wr₁₁, wr₁₀, wr₉']
  by_cases hlt : v ≤ 8
  · have hn : 8 * k + c = n := by omega_arith
    refine .inl ⟨by rw [a3₁₁, show v - c = 0 by omega_arith]; rfl, base₁₁, hm ▸ sc₉,
      fun i hi' => by rw [hm, hdata i hi', hn], hm ▸ fr, rd₁₁', wr₁₁'⟩
  · have hc : c = 8 := by omega_arith
    refine .inr ⟨fun h => ?_, base₁₁, ?_, ?_, by omega_arith, ?_, hm ▸ sc₉, ?_, hm ▸ fr, rd₁₁', wr₁₁'⟩
    · have hne : v - c ≠ 0 := by omega_arith
      rw [a3₁₁] at h
      apply hne
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
    · rw [r₁₁, o₁₀ _ (by decide), a2₉, addr_add, show 128 * k + 128 = 128 * (k + 1) by omega_arith]
    · rw [a3₁₁, show v - c = n - 8 * (k + 1) by omega_arith]
    · rw [o₁₁ _ (by decide), o₁₀ _ (by decide), a4₉]
    · rw [hm, show 8 * (k + 1) = 8 * k + c by omega_arith]; exact hdata

end VG.Proof.Camellia.RISCV64
