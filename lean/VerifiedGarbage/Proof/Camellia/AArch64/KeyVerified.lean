module

public import VerifiedGarbage.Impl.Camellia.AArch64.ExpandKey
public import VerifiedGarbage.Proof.Camellia.AArch64.Core
public import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Camellia.AArch64.Prologue
import VerifiedGarbage.Proof.Camellia.AArch64.KeyStore
import VerifiedGarbage.Proof.Camellia.AArch64.Keys
import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Crypt
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Rounds
import VerifiedGarbage.Proof.Camellia.AArch64.Group
import VerifiedGarbage.Proof.Camellia.AArch64.Crypt8
import VerifiedGarbage.Proof.Sm4.AArch64.Imm
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Camellia.AArch64.KeyContract
public import VerifiedGarbage.Proof.Camellia.KeySched
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Camellia.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The Camellia key schedule on AArch64

`expandKey_wp`: `expandKey` meets `expandKeyAArch64`. The prologue saves the
callee-saved registers; `loadKey_wp` loads `KL` and `KR` into their keySlots;
`ka_run` and `kb_run` run the pairs of rounds with `Sigma1 … Sigma6`
(`pairConst_run`: the single-block core's substitution and diffusion,
`Serial.substitute_run`, `Serial.linear_run`, on a constant) between the
XORs with `KL` and `KR`, and leave `KA` and `KB` in theirs
(`Spec.Camellia.kakb`, by `kaD_eq`); `loadValues_ok` byte-swaps the values
into registers, and `storeSubkeys_ok` stores the subkeys, which are the
specification's (`scheduleWords_expandKey`, `schedule_of_stores`). A key of
16 bytes has no `KB`: its subkeys do not use what `KB`'s keySlots hold
(`subkeyWords_128`).

`expandKey_verified`: it is correct and constant time (`expandKey_ct`).
`expandKey_framed` runs it with its working space on the stack, zeroed on
return: 160 bytes, the 20 words of the key schedule's working space.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG.Impl.Camellia (sigmas)
open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 u7 movR ldS stS eorR imm)
open VG.Proof.Camellia (pair hiW loW)
open VG.Proof.Camellia.AArch64.Serial (Constants Masks Table halves written)

/-! ## Slots and single instructions -/

theorem keySlots_eq : keySlots = 20 := rfl
theorem klSlot_eq : klSlot = 10 := rfl
theorem ksavedSlot_eq : ksavedSlot = 0 := rfl

/-! ## Saving and restoring the callee-saved registers, in the key schedule's slots -/

theorem keySavedRegs_eq : keySavedRegs = (List.range 10).map fun i => (sreg i, ksavedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def KSaved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 10, m.readW (wordAddr b (ksavedSlot + i)) 64 = s₀.gpr (sreg i)

/-- The saved registers' slots. -/
def ksavedRegion (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (8 * ksavedSlot), 80⟩

theorem ksave_ok {s : State} {b : Addr} (hw : (⟨b, 8 * keySlots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b) :
    ∃ s', runBlock isa keySaveRegs s = some s' ∧ KSaved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [ksavedRegion b] s.mem s'.mem ∧
      ∀ k, (k < ksavedSlot ∨ ksavedSlot + 10 ≤ k) → k < 2 ^ 58 → slotW s' k = slotW s k := by
  let L : List (Nat × Reg) := (List.range 10).map fun i => (ksavedSlot + i, sreg i)
  obtain hL : keySaveRegs = L.map fun x => stS x.1 x.2 := by
    rw [keySaveRegs, keySavedRegs_eq]; simp only [L, List.map_map]; rfl
  obtain hslots : L.map (·.1) = (List.range 10).map fun i => ksavedSlot + i := by
    simp only [L, List.map_map]; rfl
  rw [keySlots_eq] at hw
  obtain ⟨s', e', g', rd', wr', f', o', v'⟩ := stS_list_ok (ksavedRegion b) L s (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨by rw [ksavedSlot_eq]; omega, ⟨_, hw, ?_⟩, ?_⟩
      · rw [hb]; exact VG.Offset.contains_base b (by rw [ksavedSlot_eq]; omega) (by rw [ksavedSlot_eq]; omega)
      · rw [hb, ksavedRegion, wordAddr]
        exact VG.Offset.contains _ (by omega_using []) (by omega) (by rw [ksavedSlot_eq]; omega_using []))
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, g', rd', wr', f', fun k hk hk' => o' k ?_ hk'⟩
  · have := v' (ksavedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
    simp only [slotW, g', hb] at this
    exact this
  · rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega_using [hk, hi, h]

theorem krestore_ok {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * keySlots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hs : KSaved s₀ b s.mem) :
    ∃ s', runBlock isa keyRestoreRegs s = some s' ∧ (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 10, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  let L : List (Reg × Nat) := (List.range 10).map fun i => (sreg i, ksavedSlot + i)
  obtain hL : keyRestoreRegs = L.map fun x => ldS x.1 x.2 := by
    rw [keyRestoreRegs, keySavedRegs_eq]
  obtain hregs : L.map (·.1) = (List.range 10).map sreg := by simp only [L, List.map_map]; rfl
  rw [keySlots_eq] at hw
  obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldS_list_ok L s
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx; exact sreg_ne_sb i hi)
    (by rw [hregs]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨by rw [ksavedSlot_eq]; omega, ⟨_, List.mem_append_right _ hw, ?_⟩⟩
      rw [hb]; exact VG.Offset.contains_base b (by rw [ksavedSlot_eq]; omega) (by rw [ksavedSlot_eq]; omega))
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, fun r hr => o' r ?_, m', rd', wr'⟩
  · rw [v' (sreg i, ksavedSlot + i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩), slotW, hb]
    exact hs i hi
  · rw [hregs]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    exact fun i hi h => hr i hi h.symm

theorem slotW_eq_of {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr sb = s.gpr sb) (k : Nat) :
    slotW s' k = slotW s k := by
  simp only [slotW, hm, hb]

theorem scr_in {s : State} {b : Addr} (hscr : (⟨b, 8 * keySlots⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < keySlots) :
    InRegions s.wr (b + BitVec.ofNat 64 (8 * k)) 8 :=
  ⟨_, hscr, by rw [keySlots_eq] at hk; exact VG.Offset.contains_base _ (by rw [keySlots_eq]; omega_arith) (by omega_arith)⟩

theorem frame_slot {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk : k < keySlots) :
    Frame [⟨b, 8 * keySlots⟩] m (m.writeW (wordAddr b k) v) :=
  frame_writeW v (by rw [wordAddr]; rw [keySlots_eq] at hk; exact VG.Offset.sub_base _ (by rw [keySlots_eq]; omega_arith))

/-- `ldr d, [sb, #8 k]`. -/
theorem ldS_ok {s : State} {b : Addr} {k : Nat} (d : Reg) (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * keySlots⟩ : Region) ∈ s.wr) (hk : k < keySlots) :
    ∃ s', runBlock isa [ldS d k] s = some s' ∧ s'.gpr d = slotW s k ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have := scr_in hscr hk
  rw [← hb] at this
  exact ldMask_ok (by rw [keySlots_eq] at hk; omega_arith) (inRd this) rfl

/-- `str r, [sb, #8 k]`. -/
theorem stS_slot {s : State} {b : Addr} {k : Nat} (r : Reg) (hb : s.gpr sb = b)
    (hscr : (⟨b, 8 * keySlots⟩ : Region) ∈ s.wr) (hk : k < keySlots) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have := scr_in hscr hk
  rw [← hb] at this
  exact ⟨_, stS_ok s r (by rw [keySlots_eq] at hk; omega_arith) this, by rw [hb], rfl, rfl, rfl⟩

theorem eor_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [eorR d n m] s = some s' ∧ s'.gpr d = s.gpr n ^^^ s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.gpr n ^^^ s.gpr m), by
    simp only [eorR, runBlock_cons, runStep_some, runBlock_nil, exec_logic, read_x'],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩




theorem readW_slot_write {m : Mem} {b : Addr} {j k : Nat} (v : BitVec 64) (hj : j < keySlots) (hk : k < keySlots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 64 = if j = k then v else m.readW (wordAddr b j) 64 := by
  rw [keySlots_eq] at hj hk
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega_arith) (by omega_arith) h) (by decide)

/-- The keySlots after a store to slot `k`. -/
theorem slotW_store {s s' : State} {k : Nat} {v : BitVec 64}
    (hm : s'.mem = s.mem.writeW (wordAddr (s.gpr sb) k) v) (hg : s'.gpr = s.gpr) {j : Nat} (hj : j < keySlots)
    (hk : k < keySlots) : slotW s' j = if j = k then v else slotW s j := by
  simp only [slotW, hm, hg]; exact readW_slot_write v hj hk

/-- The words at keySlots `k` and `k + 1` hold the halves `v`. -/
def WordsAt (s : State) (k : Nat) (v : BitVec 64 × BitVec 64) : Prop :=
  WordOf (slotW s k) v.1 ∧ WordOf (slotW s (k + 1)) v.2

theorem WordsAt.congr {s s' : State} {k : Nat} {v : BitVec 64 × BitVec 64} (h : WordsAt s k v)
    (h0 : slotW s' k = slotW s k) (h1 : slotW s' (k + 1) = slotW s (k + 1)) : WordsAt s' k v :=
  ⟨h.1.congr h0, h.2.congr h1⟩

theorem kaKb_slots : klSlot = 10 ∧ krSlot = 12 ∧ klSlot = 10 ∧ kaSlot = 16 ∧ kbSlot = 18 ∧
    endSlot = 368 ∧ keySlot = 96 ∧ keySlots = 20 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `str r, [sb, #8 k]`, as keySlots. -/
theorem st_ok {s : State} {k : Nat} (r : Reg) (hscr : (⟨s.gpr sb, 8 * keySlots⟩ : Region) ∈ s.wr)
    (hk : k < keySlots) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ slotW s' k = s.gpr r ∧
      (∀ j < keySlots, j ≠ k → slotW s' j = slotW s j) ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, m, g, rd, wr⟩ := stS_slot (k := k) r rfl hscr hk
  refine ⟨s', e, ?_, fun j hj hjk => ?_, g, by rw [m]; exact frame_slot _ hk, rd, wr⟩
  · rw [slotW_store m g hk hk, ite_eq_left rfl]
  · rw [slotW_store m g hj hk, ite_eq_right hjk]

/-- `ldr d, [r, #k]`. -/
theorem ldAt_ok (s : State) (d r : Reg) {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 k) 8) :
    ∃ s', runBlock isa [.ldr .x d r k] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr r + BitVec.ofNat 64 k) 64 ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.mem.readW (s.gpr r + BitVec.ofNat 64 k) 64), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x hk hr],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r' h => RegUpd.gpr_write_of_ne _ _ _ h, rfl, rfl, rfl⟩

/-! ## Loading the key -/

/-- A step that writes only `t0`, `t1` and `u7`. -/
structure Pure (s s' : State) : Prop where
  mem : s'.mem = s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Pure.refl (s : State) : Pure s s := ⟨rfl, fun _ _ _ _ => rfl, rfl, rfl⟩

theorem Pure.trans {s₁ s₂ s₃ : State} (h₁ : Pure s₁ s₂) (h₂ : Pure s₂ s₃) : Pure s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, fun r h0 h1 h2 => (h₂.regs r h0 h1 h2).trans (h₁.regs r h0 h1 h2), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

theorem Pure.of1 {s s' : State} {d : Reg} (hd : d = t0 ∨ d = t1 ∨ d = u7) (hm : s'.mem = s.mem)
    (hg : ∀ r, r ≠ d → s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pure s s' :=
  ⟨hm, fun r h0 h1 h2 => hg r (by rcases hd with rfl | rfl | rfl <;> with_reducible assumption), hrd, hwr⟩

/-- A store of `t0` to slot `k`. -/
structure StOk (s s' : State) (k : Nat) : Prop where
  val : slotW s' k = s.gpr t0
  keep : ∀ j < keySlots, j ≠ k → slotW s' j = slotW s j
  gpr : s'.gpr = s.gpr
  frame : Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem stOk {s : State} {k : Nat} (hscr : (⟨s.gpr sb, 8 * keySlots⟩ : Region) ∈ s.wr) (hk : k < keySlots) :
    ∃ s', runBlock isa [stS k t0] s = some s' ∧ StOk s s' k := by
  obtain ⟨s', e, v, kp, g, f, rd, wr⟩ := st_ok (k := k) t0 hscr hk
  exact ⟨s', e, v, kp, g, f, rd, wr⟩

/-- `KR`'s words stored: what each branch of `loadKey` leaves. -/
structure KrPost (s s' : State) (V : BitVec 64 × BitVec 64) : Prop where
  kr : WordsAt s' krSlot V
  keep : ∀ k < keySlots, k ≠ krSlot → k ≠ krSlot + 1 → slotW s' k = slotW s k
  regs : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s'.gpr r = s.gpr r
  frame : Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem StOk.frame' {s₀ s s' : State} {k : Nat} (hf : Frame [⟨s₀.gpr sb, 8 * keySlots⟩] s₀.mem s.mem)
    (hb : s.gpr sb = s₀.gpr sb) (h : StOk s s' k) : Frame [⟨s₀.gpr sb, 8 * keySlots⟩] s₀.mem s'.mem :=
  hf.trans (by have := h.frame; rw [hb] at this; exact this)

theorem krPost_of {s s₁ s₂ s₃ s₄ : State} {V : BitVec 64 × BitVec 64}
    (p₁ : Pure s s₁) (h₂ : StOk s₁ s₂ krSlot) (p₃ : Pure s₂ s₃) (h₄ : StOk s₃ s₄ (krSlot + 1))
    (hu : WordOf (s₁.gpr t0) V.1) (hv : WordOf (s₃.gpr t0) V.2) : KrPost s s₄ V := by
  obtain ⟨-, hr, -, -, -, -, -, hS⟩ := kaKb_slots
  obtain hb₁ : s₁.gpr sb = s.gpr sb := p₁.regs _ (by decide) (by decide) (by decide)
  obtain hb₃ : s₃.gpr sb = s.gpr sb := by rw [p₃.regs _ (by decide) (by decide) (by decide), h₂.gpr, hb₁]
  obtain hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of p₁.mem hb₁
  obtain hs₃ : ∀ k, slotW s₃ k = slotW s₂ k :=
    slotW_eq_of p₃.mem (by rw [p₃.regs _ (by decide) (by decide) (by decide)])
  obtain f₂ : Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem s₂.mem :=
    StOk.frame' (by rw [p₁.mem]; exact Frame.refl _ _) hb₁ h₂
  refine ⟨⟨?_, ?_⟩, fun k hk h1 h2 => by rw [h₄.keep k hk h2, hs₃, h₂.keep k hk h1, hs₁],
    fun r h0 h1 h2 => by rw [h₄.gpr, p₃.regs r h0 h1 h2, h₂.gpr, p₁.regs r h0 h1 h2],
    StOk.frame' (by rw [p₃.mem]; exact f₂) hb₃ h₄,
    by rw [h₄.rd, p₃.rd, h₂.rd, p₁.rd], by rw [h₄.wr, p₃.wr, h₂.wr, p₁.wr]⟩
  · rw [h₄.keep _ (by omega_arith) (by omega_arith), hs₃, h₂.val]; exact hu
  · rw [h₄.val]; exact hv

theorem allOnes_eq : BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 := by decide

/-- `loadKey`: `KL`'s and `KR`'s halves, as words, in their keySlots. -/
theorem loadKey_wp {s : State} {len : Nat} (hscr : (⟨s.gpr sb, 8 * keySlots⟩ : Region) ∈ s.wr)
    (hkey : (⟨s.gpr .x0, len⟩ : Region) ∈ s.rd) (hfit : (s.gpr .x0).toNat + len ≤ 2 ^ 64)
    (hks : Region.Disjoint ⟨s.gpr .x0, len⟩ ⟨s.gpr sb, 8 * keySlots⟩)
    (hlen : s.gpr .x3 = BitVec.ofNat 64 len) (hl : len = 16 ∨ len = 24 ∨ len = 32) :
    WP isa loadKey s fun s' =>
      WordsAt s' klSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).1,
        loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).1) ∧
      WordsAt s' krSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).2,
        loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).2) ∧
      (∀ k < keySlots, (k < klSlot ∨ krSlot + 2 ≤ k) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s'.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl', hr', -, -, -, -, -, hS⟩ := kaKb_slots
  obtain ⟨hK0, hK1, hK2, hK3⟩ := Proof.Camellia.klkr_halves s.mem (s.gpr .x0) hl
  -- The key's words, read after stores to the scratch buffer.
  obtain hkw : ∀ {t : State}, t.rd = s.rd → t.gpr .x0 = s.gpr .x0 →
      Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem t.mem → ∀ d, d % 8 = 0 → d + 8 ≤ len →
      ∃ t', runBlock isa [.ldr .x t0 .x0 d] t = some t' ∧ Pure t t' ∧
        WordOf (t'.gpr t0) (Spec.Camellia.wordAt s.mem (s.gpr .x0 + BitVec.ofNat 64 d)) := by
    intro t hrd hdi hf d hd8 hd
    obtain ⟨t', e, a, o, m, rd, wr⟩ := ldAt_ok t t0 .x0 (k := d) ⟨hd8, by omega_arith⟩ (by
      rw [hrd, hdi]; exact ⟨_, List.mem_append_left _ hkey, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    refine ⟨t', e, Pure.of1 (Or.inl rfl) m o rd wr, ?_⟩
    rw [a, hdi, hf.readW (r := ⟨s.gpr .x0 + BitVec.ofNat 64 d, 64 / 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hks.sub_left (VG.Offset.sub_base _ (by omega_arith))) (by decide)]
    exact wordOf_readW _ _
  obtain hz : s.gpr .x0 + BitVec.ofNat 64 0 = s.gpr .x0 := by simp
  obtain hscrOf : ∀ {t : State}, t.gpr sb = s.gpr sb → t.wr = s.wr → (⟨t.gpr sb, 8 * keySlots⟩ : Region) ∈ t.wr :=
    fun hb hw => by rw [hb, hw]; exact hscr
  obtain hn : ∀ {r : Reg}, r = t0 ∨ r = t1 ∨ r = u7 → sb ≠ r ∧ Reg.x0 ≠ r ∧ Reg.x3 ≠ r := by
    intro r hr; rcases hr with rfl | rfl | rfl <;> decide
  unfold loadKey
  -- `KL`.
  obtain ⟨s₁, e₁, p₁, w₁⟩ := hkw rfl rfl (Frame.refl _ _) 0 (by decide) (by omega_arith)
  obtain hb₁ : s₁.gpr sb = s.gpr sb := p₁.regs _ (by decide) (by decide) (by decide)
  obtain ⟨s₂, e₂, h₂⟩ := stOk (k := klSlot) (hscrOf hb₁ p₁.wr) (by omega_arith)
  obtain hb₂ : s₂.gpr sb = s.gpr sb := by rw [h₂.gpr, hb₁]
  obtain f₂ := StOk.frame' (by rw [p₁.mem]; exact Frame.refl _ _) hb₁ h₂
  obtain ⟨s₃, e₃, p₃, w₃⟩ := hkw (by rw [h₂.rd, p₁.rd]) (by rw [h₂.gpr, p₁.regs _ (by decide) (by decide) (by decide)])
    f₂ 8 (by decide) (by omega_arith)
  obtain hb₃ : s₃.gpr sb = s.gpr sb := by rw [p₃.regs _ (by decide) (by decide) (by decide), hb₂]
  obtain ⟨s₄, e₄, h₄⟩ := stOk (k := klSlot + 1) (hscrOf hb₃ (by rw [p₃.wr, h₂.wr, p₁.wr])) (by omega_arith)
  obtain f₄ := StOk.frame' (by rw [p₃.mem]; exact f₂) hb₃ h₄
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ t1 .x3 (imm := 16) (by decide)
  obtain p₅ : Pure s₄ s₅ := Pure.of1 (Or.inr (Or.inl rfl)) m₅ g₅ rd₅ wr₅
  obtain hg₅ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ u7 → s₅.gpr r = s.gpr r := fun r h0 h1 h2 => by
    rw [p₅.regs r h0 h1 h2, h₄.gpr, p₃.regs r h0 h1 h2, h₂.gpr, p₁.regs r h0 h1 h2]
  obtain hb₅ : s₅.gpr sb = s.gpr sb := hg₅ _ (by decide) (by decide) (by decide)
  obtain hs₅ : ∀ k, slotW s₅ k = slotW s₄ k := slotW_eq_of m₅ (p₅.regs _ (by decide) (by decide) (by decide))
  obtain hs₃ : ∀ k, slotW s₃ k = slotW s₂ k :=
    slotW_eq_of p₃.mem (p₃.regs _ (by decide) (by decide) (by decide))
  obtain hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of p₁.mem hb₁
  obtain f₅ : Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem s₅.mem := by rw [m₅]; exact f₄
  obtain rd₅' : s₅.rd = s.rd := by rw [rd₅, h₄.rd, p₃.rd, h₂.rd, p₁.rd]
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, h₄.wr, p₃.wr, h₂.wr, p₁.wr]
  obtain hkl : WordsAt s₅ klSlot (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).1,
      loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).1) := by
    refine ⟨?_, ?_⟩
    · rw [hs₅, h₄.keep _ (by omega_arith) (by omega_arith), hs₃, h₂.val, hK0, ← hz]; exact w₁
    · rw [hs₅, h₄.val, hK1]; exact w₃
  obtain hother : ∀ k < keySlots, k ≠ klSlot → k ≠ klSlot + 1 → slotW s₅ k = slotW s k := fun k hk h1 h2 => by
    rw [hs₅, h₄.keep k hk h2, hs₃, h₂.keep k hk h1, hs₁]
  obtain hx3 : s₄.gpr .x3 = BitVec.ofNat 64 len := by
    rw [h₄.gpr, p₃.regs _ (by decide) (by decide) (by decide), h₂.gpr, p₁.regs _ (by decide) (by decide) (by decide),
      hlen]
  obtain hz₅ : (s₅.gpr t1 == 0) = decide (len = 16) := by
    rw [z₅, hx3, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [show ([.ldr .x t0 .x0 0, stS klSlot t0, .ldr .x t0 .x0 8, stS (klSlot + 1) t0,
        .subImm .x t1 .x3 16] : List Instr) =
        [.ldr .x t0 .x0 0] ++ ([stS klSlot t0] ++ ([.ldr .x t0 .x0 8] ++
          ([stS (klSlot + 1) t0] ++ [.subImm .x t1 .x3 16]))) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅], ?_⟩)
  refine WP.mono (Q := fun s' => KrPost s₅ s' (hiW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).2,
      loW (Spec.Camellia.klkr (Spec.Camellia.bytesAt s.mem (s.gpr .x0) len)).2))
    (WP.ite (decide (len = 16)) ((eval_zero s₅ t1).trans (by rw [hz₅])) (fun h16 => ?_) (fun h16 => ?_))
    fun s' h => ?_
  · -- A key of 16 bytes: `KR = 0`.
    obtain h16 : len = 16 := by simpa using h16
    obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆⟩ := movz_ok s₅ t0 (v := 0) (by decide)
    obtain p₆ : Pure s₅ s₆ := Pure.of1 (Or.inl rfl) m₆ o₆ rd₆ wr₆
    obtain ⟨s₇, e₇, h₇⟩ := stOk (k := krSlot) (hscrOf (by rw [o₆ _ (by decide), hb₅]) (by rw [wr₆, wr₅']))
      (by omega_arith)
    obtain ⟨s₈, e₈, h₈⟩ := stOk (k := krSlot + 1)
      (hscrOf (by rw [h₇.gpr, o₆ _ (by decide), hb₅]) (by rw [h₇.wr, wr₆, wr₅'])) (by omega_arith)
    refine WP.of_runBlock ⟨s₈, by
      rw [show ([.movz .x t0 0 0, stS krSlot t0, stS (krSlot + 1) t0] : List Instr) =
          [.movz .x t0 (BitVec.ofNat 16 0) 0] ++ ([stS krSlot t0] ++ [stS (krSlot + 1) t0]) from rfl,
        runBlock_append', e₆, Option.bind_some, runBlock_append', e₇, Option.bind_some, e₈],
      krPost_of p₆ h₇ (Pure.refl _) h₈ (by rw [a₆, hK2, ite_eq_left h16]; exact WordOf.zero)
        (by rw [h₇.gpr, a₆, hK3, ite_eq_left h16]; exact WordOf.zero)⟩
  · have h16 : len ≠ 16 := by simpa using h16
    obtain ⟨s₆, e₆, p₆, w₆⟩ := hkw (by rw [rd₅']) (hg₅ _ (by decide) (by decide) (by decide)) f₅ 16
      (by decide) (by omega_arith)
    obtain hb₆ : s₆.gpr sb = s.gpr sb := by rw [p₆.regs _ (by decide) (by decide) (by decide), hb₅]
    obtain ⟨s₇, e₇, h₇⟩ := stOk (k := krSlot) (hscrOf hb₆ (by rw [p₆.wr, wr₅'])) (by omega_arith)
    obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := subI_ok s₇ t1 .x3 (imm := 24) (by decide)
    obtain p₈ : Pure s₇ s₈ := Pure.of1 (Or.inr (Or.inl rfl)) m₈ g₈ rd₈ wr₈
    obtain hb₈ : s₈.gpr sb = s.gpr sb := by rw [p₈.regs _ (by decide) (by decide) (by decide), h₇.gpr, hb₆]
    obtain f₈ : Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem s₈.mem := by
      rw [m₈]; exact StOk.frame' (by rw [p₆.mem]; exact f₅) hb₆ h₇
    obtain hz₈ : (s₈.gpr t1 == 0) = decide (len = 24) := by
      rw [z₈, h₇.gpr, p₆.regs _ (by decide) (by decide) (by decide), hg₅ _ (by decide) (by decide) (by decide),
        hlen, VG.Offset.ofNat_sub_ofNat_beq (by omega_arith) (by decide)]
    refine WP.seq (WP.of_runBlock ⟨s₈, by
      rw [show ([.ldr .x t0 .x0 16, stS krSlot t0, .subImm .x t1 .x3 24] : List Instr) =
          [.ldr .x t0 .x0 16] ++ ([stS krSlot t0] ++ [.subImm .x t1 .x3 24]) from rfl,
        runBlock_append', e₆, Option.bind_some, runBlock_append', e₇, Option.bind_some, e₈], ?_⟩)
    refine WP.ite (decide (len = 24)) ((eval_zero s₈ t1).trans (by rw [hz₈])) (fun h24 => ?_) (fun h24 => ?_)
    · have h24 : len = 24 := by simpa using h24
      obtain ⟨s₉a, e₉a, a₉a, o₉a, m₉a, rd₉a, wr₉a⟩ := movz_ok s₈ u7 (v := 0) (by decide)
      obtain ⟨s₉b, e₉b, a₉b, o₉b, m₉b, rd₉b, wr₉b⟩ := subI_ok s₉a u7 u7 (imm := 1) (by decide)
      obtain ⟨s₉, e₉, a₉, o₉, m₉, rd₉, wr₉⟩ := eor_ok s₉b t0 t0 u7
      obtain p₉ : Pure s₈ s₉ := (Pure.of1 (Or.inr (Or.inr rfl)) m₉a o₉a rd₉a wr₉a).trans
        ((Pure.of1 (Or.inr (Or.inr rfl)) m₉b o₉b rd₉b wr₉b).trans (Pure.of1 (Or.inl rfl) m₉ o₉ rd₉ wr₉))
      obtain hnot : s₉.gpr t0 = ~~~ s₈.gpr t0 := by
        rw [a₉, o₉b _ (by decide), o₉a _ (by decide), a₉b, a₉a, allOnes_eq, BitVec.xor_allOnes]
      obtain ⟨s₁₀, e₁₀, h₁₀⟩ := stOk (k := krSlot + 1)
        (hscrOf (by rw [p₉.regs _ (by decide) (by decide) (by decide), hb₈])
          (by rw [p₉.wr, wr₈, h₇.wr, p₆.wr, wr₅'])) (by omega_arith)
      refine WP.of_runBlock ⟨s₁₀, by
        rw [show ([.movz .x u7 0 0, .subImm .x u7 u7 1, eorR t0 t0 u7, stS (krSlot + 1) t0] : List Instr) =
            [.movz .x u7 (BitVec.ofNat 16 0) 0] ++ ([.subImm .x u7 u7 1] ++ ([eorR t0 t0 u7] ++
              [stS (krSlot + 1) t0])) from rfl,
          runBlock_append', e₉a, Option.bind_some, runBlock_append', e₉b, Option.bind_some,
          runBlock_append', e₉, Option.bind_some, e₁₀],
        krPost_of p₆ h₇ (p₈.trans p₉) h₁₀ (by rw [hK2, ite_eq_right h16]; exact w₆)
          (by rw [hnot, g₈ _ (by decide), h₇.gpr, hK3, ite_eq_right h16, ite_eq_left h24]; exact w₆.not)⟩
    · have h24 : len ≠ 24 := by simpa using h24
      obtain ⟨s₉, e₉, p₉, w₉⟩ := hkw (by rw [rd₈, h₇.rd, p₆.rd, rd₅'])
        (by rw [g₈ _ (by decide), h₇.gpr, p₆.regs _ (by decide) (by decide) (by decide),
          hg₅ _ (by decide) (by decide) (by decide)]) f₈ 24 (by decide) (by omega_arith)
      obtain ⟨s₁₀, e₁₀, h₁₀⟩ := stOk (k := krSlot + 1)
        (hscrOf (by rw [p₉.regs _ (by decide) (by decide) (by decide), hb₈])
          (by rw [p₉.wr, wr₈, h₇.wr, p₆.wr, wr₅'])) (by omega_arith)
      refine WP.of_runBlock ⟨s₁₀, by
        rw [show ([.ldr .x t0 .x0 24, stS (krSlot + 1) t0] : List Instr) =
            [.ldr .x t0 .x0 24] ++ [stS (krSlot + 1) t0] from rfl,
          runBlock_append', e₉, Option.bind_some, e₁₀],
        krPost_of p₆ h₇ (p₈.trans p₉) h₁₀ (by rw [hK2, ite_eq_right h16]; exact w₆)
          (by rw [hK3, ite_eq_right h16, ite_eq_right h24]; exact w₉)⟩
  · -- Both.
    refine ⟨hkl.congr (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)) (h.keep _ (by omega_arith) (by omega_arith) (by omega_arith)),
      h.kr, fun k hk h1 => by rw [h.keep k hk (by omega_arith) (by omega_arith), hother k hk (by omega_arith) (by omega_arith)],
      fun r h0 h1 h2 => by rw [h.regs r h0 h1 h2, hg₅ r h0 h1 h2],
      f₅.trans (by have := h.frame; rw [hb₅] at this; exact this),
      by rw [h.rd, rd₅'], by rw [h.wr, wr₅']⟩

/-! ## Loading the values -/

def lvChunk (v k : Nat) : List Instr :=
  [ldS (hiReg v) k, .rev (hiReg v) (hiReg v), ldS (loReg v) (k + 1), .rev (loReg v) (loReg v)]

theorem loadValues_eq :
    loadValues = lvChunk 0 klSlot ++ (lvChunk 1 krSlot ++ (lvChunk 2 kaSlot ++ lvChunk 3 kbSlot)) := rfl

theorem regs_lt4 {v : Nat} (hv : v < 4) : hiReg v ≠ sb ∧ loReg v ≠ sb ∧ hiReg v ≠ loReg v := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> decide

theorem lvChunk_ok {s : State} {v k : Nat} (hv : v < 4) (hscr : (⟨s.gpr sb, 8 * keySlots⟩ : Region) ∈ s.wr)
    (hk : k + 1 < keySlots) :
    ∃ s', runBlock isa (lvChunk v k) s = some s' ∧ s'.gpr (hiReg v) = rev64 (slotW s k) ∧
      s'.gpr (loReg v) = rev64 (slotW s (k + 1)) ∧
      (∀ r, r ≠ hiReg v → r ≠ loReg v → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨n1, n2, n3⟩ := regs_lt4 hv
  obtain ⟨s₁, e₁, a₁, o₁, m₁, rd₁, wr₁⟩ := ldS_ok (k := k) (hiReg v) rfl hscr (by omega_arith)
  obtain ⟨s₂, e₂, a₂, o₂, m₂, rd₂, wr₂⟩ := rev_ok s₁ (hiReg v) (hiReg v)
  obtain hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ n1.symm, o₁ _ n1.symm]
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := ldS_ok (k := k + 1) (loReg v) hb₂ (by rw [wr₂, wr₁]; exact hscr) hk
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := rev_ok s₃ (loReg v) (loReg v)
  refine ⟨s₄, ?_, ?_, ?_, fun r h1 h2 => by rw [o₄ r h2, o₃ r h2, o₂ r h1, o₁ r h1],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  · rw [lvChunk, show ([ldS (hiReg v) k, .rev (hiReg v) (hiReg v), ldS (loReg v) (k + 1),
        .rev (loReg v) (loReg v)] : List Instr) = [ldS (hiReg v) k] ++ ([.rev (hiReg v) (hiReg v)] ++
          ([ldS (loReg v) (k + 1)] ++ [.rev (loReg v) (loReg v)])) from rfl,
      runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, e₄]
  · rw [o₄ _ n3, o₃ _ n3, a₂, a₁]
  · rw [a₄, a₃, slotW_eq_of (by rw [m₂, m₁]) hb₂]

/-- `loadValues`: the four values' halves, byte-swapped into `hiReg v` and `loReg v`. -/
theorem loadValues_ok {s : State} (hscr : (⟨s.gpr sb, 8 * keySlots⟩ : Region) ∈ s.wr) (vs : List (BitVec 128))
    (hw : ∀ v < 4, WordsAt s ([klSlot, krSlot, kaSlot, kbSlot].getD v 0) (hiW (vs.getD v 0), loW (vs.getD v 0))) :
    ∃ s', runBlock isa loadValues s = some s' ∧
      (∀ v < 4, s'.gpr (hiReg v) = hiW (vs.getD v 0) ∧ s'.gpr (loReg v) = loW (vs.getD v 0)) ∧
      (∀ r, (∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hl, hr, hW, hA, hB, -, -, hS⟩ := kaKb_slots
  obtain ⟨s₁, e₁, h₁, l₁, o₁, m₁, rd₁, wr₁⟩ := lvChunk_ok (v := 0) (k := klSlot) (by decide) hscr (by omega_arith)
  obtain hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (by decide) (by decide)
  obtain hs₁ : ∀ k, slotW s₁ k = slotW s k := slotW_eq_of m₁ hb₁
  obtain ⟨s₂, e₂, h₂, l₂, o₂, m₂, rd₂, wr₂⟩ := lvChunk_ok (v := 1) (k := krSlot) (by decide)
    (by rw [hb₁, wr₁]; exact hscr) (by omega_arith)
  obtain hb₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide) (by decide), hb₁]
  obtain hs₂ : ∀ k, slotW s₂ k = slotW s k := fun k => by rw [slotW_eq_of m₂ (by rw [hb₂, hb₁]), hs₁]
  obtain ⟨s₃, e₃, h₃, l₃, o₃, m₃, rd₃, wr₃⟩ := lvChunk_ok (v := 2) (k := kaSlot) (by decide)
    (by rw [hb₂, wr₂, wr₁]; exact hscr) (by omega_arith)
  obtain hb₃ : s₃.gpr sb = s.gpr sb := by rw [o₃ _ (by decide) (by decide), hb₂]
  obtain hs₃ : ∀ k, slotW s₃ k = slotW s k := fun k => by rw [slotW_eq_of m₃ (by rw [hb₃, hb₂]), hs₂]
  obtain ⟨s₄, e₄, h₄, l₄, o₄, m₄, rd₄, wr₄⟩ := lvChunk_ok (v := 3) (k := kbSlot) (by decide)
    (by rw [hb₃, wr₃, wr₂, wr₁]; exact hscr) (by omega_arith)
  refine ⟨s₄, by rw [loadValues_eq, runBlock_append', e₁, Option.bind_some, runBlock_append', e₂,
      Option.bind_some, runBlock_append', e₃, Option.bind_some, e₄], fun v hv => ?_,
    fun r hr => by
      obtain ⟨a0, b0⟩ := hr 0 (by decide); obtain ⟨a1, b1⟩ := hr 1 (by decide)
      obtain ⟨a2, b2⟩ := hr 2 (by decide); obtain ⟨a3, b3⟩ := hr 3 (by decide)
      rw [o₄ r a3 b3, o₃ r a2 b2, o₂ r a1 b1, o₁ r a0 b0],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁]⟩
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_arith) with rfl | rfl | rfl | rfl
  · have w := hw 0 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), o₂ _ (by decide) (by decide), h₁]
      exact rev_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), o₂ _ (by decide) (by decide), l₁]
      exact rev_of_wordOf w.2
  · have w := hw 1 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), h₂, hs₁]
      exact rev_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), l₂, hs₁]
      exact rev_of_wordOf w.2
  · have w := hw 2 (by decide)
    refine ⟨?_, ?_⟩
    · rw [o₄ _ (by decide) (by decide), h₃, hs₂]; exact rev_of_wordOf w.1
    · rw [o₄ _ (by decide) (by decide), l₃, hs₂]; exact rev_of_wordOf w.2
  · have w := hw 3 (by decide)
    exact ⟨by rw [h₄, hs₃]; exact rev_of_wordOf w.1, by rw [l₄, hs₃]; exact rev_of_wordOf w.2⟩

theorem sreg_ne' (i : Nat) (hi : i < 10) : sreg i ≠ sb ∧ sreg i ≠ .x3 := by
  revert i; decide

/-! ## The pairs of rounds -/

/-- `eor d, n, m`, which leaves the vector registers. -/
theorem eorV_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.logic .eor .x d n m] s = some s' ∧ s'.gpr d = s.gpr n ^^^ s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v :=
  ⟨s.write .x d (s.gpr n ^^^ s.gpr m), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_logic, read_x'],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `imm` writes no vector register. -/
theorem imm_v (d : Reg) (x : BitVec 64) : (imm d x).all (fun i => vdstOf i == none) = true := by
  refine List.all_eq_true.mpr fun i hi => ?_
  simp only [imm, List.mem_cons, List.mem_map] at hi
  rcases hi with rfl | ⟨k, -, rfl⟩ <;> rfl

/-- The constants, the masks and the table, in a state with the same vector
registers and masks. -/
theorem tab_of {s t : State} (hv : t.v = s.v) (hg : ∀ r ∈ Serial.maskRegs, t.gpr r = s.gpr r)
    (hc : Constants s) (hm : Masks s) (ht : Table s) : Constants t ∧ Masks t ∧ Table t :=
  ⟨by simpa only [Constants, hv] using hc, hm.of_regs hg, by simpa only [Table, hv] using ht⟩

/-- `b ^= F(a, x)`. -/
theorem fConst_run {s : State} {a b : Reg} (x : BitVec 64)
    (ha : a = .x6 ∨ a = .x7) (hb : b = .x6 ∨ b = .x7)
    (hc : Constants s) (hm : Masks s) (ht : Table s) :
    ∃ t, runBlock isa (fConst a b x) s = some t ∧
      t.gpr b = s.gpr b ^^^ Spec.Camellia.f (s.gpr a) x ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ r, r ≠ b → r ∉ [.x8, .x10, .x11, .x12, .x16, .x17] → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ha8 : a ≠ .x8 := by rcases ha with rfl | rfl <;> decide
  obtain hb8 : b ≠ .x8 := by rcases hb with rfl | rfl <;> decide
  obtain hb10 : b ≠ .x10 := by rcases hb with rfl | rfl <;> decide
  obtain hbl : b ∉ [.x10, .x11, .x12, .x16, .x17] := by rcases hb with rfl | rfl <;> decide
  obtain ⟨p, pe, pv, pg, pm, prd, pwr⟩ := VG.Proof.Sm4.AArch64.imm_ok s .x8 x
  obtain pvec : p.v = s.v := VG.AArch64.Tbl.runBlock_v (imm_v _ _) pe
  obtain ⟨u, ue, uv, ug, um, urd, uwr, uvec⟩ := eorV_ok p .x10 a .x8
  obtain uvec' : u.v = s.v := uvec.trans pvec
  obtain ug' : ∀ r, r ≠ .x8 → r ≠ .x10 → u.gpr r = s.gpr r := fun r h8 h10 => (ug r h10).trans (pg r h8)
  obtain uv' : u.gpr .x10 = s.gpr a ^^^ x := by rw [uv, pg a ha8, pv]
  obtain ⟨uc, umat, ut⟩ := tab_of uvec' (fun r hr => ug' r (by revert r; decide) (by revert r; decide)) hc hm ht
  obtain ⟨v, ve, vv, vg, vm, vrd, vwr, -, vvec⟩ := Serial.substitute_run u uc umat ut
  obtain ⟨w, we, wv, wg, wm, wrd, wwr, -, wvec⟩ := Serial.linear_run v
  let t := w.write .x b (w.read .x b ^^^ w.read .x .x10)
  obtain wb : w.read .x b = s.gpr b := by
    simp only [State.read, Size.bits, BitVec.setWidth_eq, wg _ hbl, vg _ hbl, ug' _ hb8 hb10]
  obtain val : w.read .x .x10 = Spec.Camellia.f (s.gpr a) x := by
    simp only [State.read, Size.bits, BitVec.setWidth_eq, wv, vv, uv']
    exact (VG.Proof.Camellia.Serial.f_eq _ _).symm
  obtain other : ∀ r, r ≠ b → r ∉ [.x8, .x10, .x11, .x12, .x16, .x17] → t.gpr r = s.gpr r := by
    intro r hr hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain h5 : r ∉ [.x10, .x11, .x12, .x16, .x17] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact hn.2
    rw [RegUpd.gpr_write_of_ne _ _ _ hr, wg _ h5, vg _ h5, ug' _ hn.1 hn.2.1]
  obtain tv : ∀ q, q ∉ [.v0, .v1, .v2, .v3] → t.v q = s.v q := by
    intro q hq
    rw [show t.v q = w.v q from rfl, wvec, vvec _ hq, uvec']
  obtain tt : Table t := by
    intro j hj
    rw [VG.AArch64.Tbl.tbyte_congr' (fun i hi => tv _ (by
      obtain hn := VG.AArch64.Tbl.treg_ne i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩)) j hj]
    exact ht j hj
  refine ⟨t, ?_, ?_, ?_, ?_, tt, other, wm.trans (vm.trans (um.trans pm)),
    wrd.trans (vrd.trans (urd.trans prd)), wwr.trans (vwr.trans (uwr.trans pwr))⟩
  · rw [fConst, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, pe, Option.bind_some, ue,
      Option.bind_some, ve, Option.bind_some, we, Option.bind_some]
    rfl
  · simp only [t, RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, wb, val]
  · exact ⟨(tv _ (by decide)).trans hc.1, (tv _ (by decide)).trans hc.2.1, (tv _ (by decide)).trans hc.2.2⟩
  · exact hm.of_regs fun r hr => other r (by rcases hb with rfl | rfl <;> (revert r; decide)) (by revert r; decide)

/-- Two rounds with the constants `x` and `y`. -/
theorem pairConst_run (s : State) (x y : BitVec 64) (hc : Constants s) (hm : Masks s) (ht : Table s) :
    ∃ t, runBlock isa (pairConst x y) s = some t ∧ halves t = pair x y (halves s) ∧
      Constants t ∧ Masks t ∧ Table t ∧ (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨u, ue, uv, uc, um, ut, ug, umem, urd, uwr⟩ :=
    fConst_run (a := .x6) (b := .x7) x (Or.inl rfl) (Or.inr rfl) hc hm ht
  obtain ⟨v, ve, vv, vc, vm, vt, vg, vmem, vrd, vwr⟩ :=
    fConst_run (a := .x7) (b := .x6) y (Or.inr rfl) (Or.inl rfl) uc um ut
  refine ⟨v, ?_, ?_, vc, vm, vt, ?_, vmem.trans umem, vrd.trans urd, vwr.trans uwr⟩
  · rw [pairConst, VG.Interleave.runBlock_append, ue, Option.bind_some, ve]
  · simp only [halves, pair]
    rw [vv, vg .x7 (by decide) (by decide), uv, ug .x6 (by decide) (by decide)]
  · intro r hr
    obtain h6 : r ≠ .x6 := fun h => hr (h ▸ (by decide : Reg.x6 ∈ written))
    obtain h7 : r ≠ .x7 := fun h => hr (h ▸ (by decide : Reg.x7 ∈ written))
    obtain hrest : r ∉ [.x8, .x10, .x11, .x12, .x16, .x17] := fun h =>
      hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    exact (vg r h6 hrest).trans (ug r h7 hrest)

/-! ## The values between the pairs -/

theorem wordOf_rev (h : BitVec 64) : WordOf (rev64 h) h := fun i hi j hj => by
  obtain e := rev64_bit h (i := 7 - i) (j := j) (by omega_arith) hj
  rw [show 56 - 8 * (7 - i) + j = 8 * i + j by omega_arith] at e
  rw [e, Camellia.getLsbD_byteOf _ hi hj]; congr 1; omega_arith

theorem wordOf_self_rev (w : BitVec 64) : WordOf w (rev64 w) := fun i hi j hj => by
  rw [Camellia.getLsbD_byteOf _ hi hj, rev64_bit w hi hj]

/-- A slot of the scratch buffer is readable. -/
theorem slot_rd {s : State} (hscr : (⟨s.gpr sb, 8 * keySlots⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < keySlots) :
    InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (8 * k)) 8 := inRd (scr_in hscr hk)

/-- `xorValue k`: the value at keySlots `k` and `k + 1` XORed into the halves. -/
theorem xorValue_run {s : State} {k : Nat} (hscr : (⟨s.gpr sb, 8 * keySlots⟩ : Region) ∈ s.wr)
    (hk : k + 1 < keySlots) :
    ∃ t, runBlock isa (xorValue k) s = some t ∧
      halves t = ((halves s).1 ^^^ rev64 (slotW s k), (halves s).2 ^^^ rev64 (slotW s (k + 1))) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.v = s.v := by
  have hS := keySlots_eq
  obtain ⟨a, ae, av, ag, am, ard, awr, -, avec⟩ := Serial.loadBE_run (s := s) (r := .x8) (off := 8 * k)
    ⟨by omega_arith, by omega_arith⟩ (slot_rd hscr (by omega_arith))
  obtain ⟨b, be, bv, bg, bm, brd, bwr, bvec⟩ := eorV_ok a .x6 .x6 .x8
  obtain hb5 : b.gpr .x5 = s.gpr .x5 := by rw [bg _ (by decide), ag _ (by decide)]
  obtain ⟨c, ce, cv, cg, cm, crd, cwr, -, cvec⟩ := Serial.loadBE_run (s := b) (r := .x8) (off := 8 * (k + 1))
    ⟨by omega_arith, by omega_arith⟩ (by rw [brd, ard, bwr, awr, hb5]; exact slot_rd hscr hk)
  obtain ⟨d, de, dv, dg, dm, drd, dwr, dvec⟩ := eorV_ok c .x7 .x7 .x8
  refine ⟨d, ?_, ?_, fun r h6 h7 h8 => by rw [dg r h7, cg r h8, bg r h6, ag r h8],
    by rw [dm, cm, bm, am], by rw [drd, crd, brd, ard], by rw [dwr, cwr, bwr, awr],
    by rw [dvec, cvec, bvec, avec]⟩
  · rw [xorValue, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append, ae, Option.bind_some, be, Option.bind_some, ce, Option.bind_some, de]
  · have e6 : d.gpr .x6 = s.gpr .x6 ^^^ rev64 (slotW s k) := by
      rw [dg _ (by decide), cg _ (by decide), bv, ag _ (by decide), av]; rfl
    obtain e7 : d.gpr .x7 = s.gpr .x7 ^^^ rev64 (slotW s (k + 1)) := by
      rw [dv, cg _ (by decide), cv, bg _ (by decide), ag _ (by decide), bm, am, hb5]; rfl
    simp only [halves, e6, e7]

/-- `storeValue k`: the halves, as words, to keySlots `k` and `k + 1`. -/
theorem storeValue_run {s : State} {k : Nat} (hscr : (⟨s.gpr sb, 8 * keySlots⟩ : Region) ∈ s.wr)
    (hk : k + 1 < keySlots) :
    ∃ t, runBlock isa (storeValue k) s = some t ∧ WordsAt t k (halves s) ∧
      (∀ j < keySlots, j ≠ k → j ≠ k + 1 → slotW t j = slotW s j) ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v := by
  obtain ⟨a, ae, av, ag, am, ard, awr⟩ := rev_ok s .x8 .x6
  obtain ha : a.gpr sb = s.gpr sb := ag _ (by decide)
  obtain ⟨b, be, bv, bk, bg, bf, brd, bwr⟩ := st_ok (s := a) (k := k) .x8 (by rw [ha, awr]; exact hscr)
    (by omega_arith)
  obtain hb : b.gpr sb = s.gpr sb := by rw [bg, ha]
  obtain ⟨c, ce, cv, cg, cm, crd, cwr⟩ := rev_ok b .x8 .x7
  obtain hc : c.gpr sb = s.gpr sb := by rw [cg _ (by decide), hb]
  obtain ⟨d, de, dv, dk, dg, df, drd, dwr⟩ := st_ok (s := c) (k := k + 1) .x8
    (by rw [hc, cwr, bwr, awr]; exact hscr) hk
  obtain e : runBlock isa (storeValue k) s = some d := by
    rw [storeValue, show ([.rev .x8 .x6, stS k .x8, .rev .x8 .x7, stS (k + 1) .x8] : List Instr) =
        [.rev .x8 .x6] ++ ([stS k .x8] ++ ([.rev .x8 .x7] ++ [stS (k + 1) .x8])) from rfl,
      runBlock_append', ae, Option.bind_some, runBlock_append', be, Option.bind_some,
      runBlock_append', ce, Option.bind_some, de]
  obtain hcs : ∀ j, slotW c j = slotW b j := slotW_eq_of cm (cg _ (by decide))
  obtain has : ∀ j, slotW a j = slotW s j := slotW_eq_of am ha
  refine ⟨d, e, ⟨?_, ?_⟩, fun j hj h0 h1 => by rw [dk j hj h1, hcs, bk j hj h0, has],
    fun r hr => by rw [dg, cg r hr, bg, ag r hr], ?_, by rw [drd, crd, brd, ard],
    by rw [dwr, cwr, bwr, awr], VG.AArch64.Tbl.runBlock_v rfl e⟩
  · rw [dk k (by omega_arith) (by omega_arith), hcs, bv, av]; exact wordOf_rev _
  · rw [dv, cv, bg, ag _ (by decide)]; exact wordOf_rev _
  · rw [ha] at bf; rw [hc] at df; rw [am] at bf; rw [cm] at df
    exact bf.trans df

/-- `ka`: `KA` in the halves and in its keySlots. -/
theorem ka_run {s : State} {KL KR : BitVec 64 × BitVec 64}
    (hscr : (⟨s.gpr sb, 8 * keySlots⟩ : Region) ∈ s.wr) (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hkl : WordsAt s klSlot KL) (hkr : WordsAt s krSlot KR) :
    ∃ t, runBlock isa ka s = some t ∧ halves t = kaD2 KL KR ∧ WordsAt t kaSlot (kaD2 KL KR) ∧
      Constants t ∧ Masks t ∧ Table t ∧
      (∀ j < keySlots, j ≠ kaSlot → j ≠ kaSlot + 1 → slotW t j = slotW s j) ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨hl, hr, -, hA, hB, -, -, hS⟩ := kaKb_slots
  obtain nw : ∀ {r : Reg}, r ∉ written → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 := fun {r} h =>
    ⟨fun e => h (e ▸ by decide), fun e => h (e ▸ by decide), fun e => h (e ▸ by decide)⟩
  -- `KL` into the halves.
  obtain ⟨a, ae, av, ag, am, ard, awr, -, avec⟩ := Serial.loadBE_run (s := s) (r := .x6) (off := 8 * klSlot)
    ⟨by decide, by decide⟩ (slot_rd hscr (by omega_arith))
  obtain ha5 : a.gpr .x5 = s.gpr .x5 := ag _ (by decide)
  obtain ⟨b, be, bv, bg, bm, brd, bwr, -, bvec⟩ := Serial.loadBE_run (s := a) (r := .x7)
    (off := 8 * (klSlot + 1)) ⟨by decide, by decide⟩ (by rw [ard, awr, ha5]; exact slot_rd hscr (by omega_arith))
  obtain hb5 : b.gpr sb = s.gpr sb := by rw [bg _ (by decide)]; exact ha5
  obtain hbs : ∀ j, slotW b j = slotW s j := slotW_eq_of (bm.trans am) hb5
  obtain hbw : b.wr = s.wr := bwr.trans awr
  obtain hbh : halves b = KL := by
    obtain e6 : b.gpr .x6 = KL.1 := by rw [bg _ (by decide), av]; exact rev_of_wordOf hkl.1
    obtain e7 : b.gpr .x7 = KL.2 := by rw [bv, am, ha5]; exact rev_of_wordOf hkl.2
    simp only [halves, e6, e7]
  obtain ⟨cb, cmk, ctb⟩ := tab_of (bvec.trans avec)
    (fun r hr => (bg r (by revert r; decide)).trans (ag r (by revert r; decide))) hc hm ht
  -- `KL ^ KR`, and the first pair.
  obtain ⟨c, ce, ch, cg, cm, crd, cwr, cvec⟩ := xorValue_run (s := b) (k := krSlot)
    (by rw [hb5, hbw]; exact hscr) (by omega_arith)
  obtain ⟨cc, cmk', ct⟩ := tab_of cvec
    (fun r hr => cg r (by revert r; decide) (by revert r; decide) (by revert r; decide)) cb cmk ctb
  obtain ⟨d, de, dh, dc, dmk, dt, dg, dm, drd, dwr⟩ :=
    pairConst_run c Spec.Camellia.sigma1 Spec.Camellia.sigma2 cc cmk' ct
  obtain hd5 : d.gpr sb = s.gpr sb := by
    rw [dg _ (by decide), cg _ (by decide) (by decide) (by decide), hb5]
  obtain hds : ∀ j, slotW d j = slotW s j := fun j => by
    rw [slotW_eq_of (dm.trans cm) (by rw [hd5, hb5]), hbs]
  obtain hdw : d.wr = s.wr := by rw [dwr, cwr, hbw]
  obtain hdh : halves d = kaD1 KL KR := by
    rw [dh, ch, hbh, hbs, hbs, rev_of_wordOf hkr.1, rev_of_wordOf hkr.2]; rfl
  -- `^ KL`, and the second pair.
  obtain ⟨e, ee, eh, eg, em, erd, ewr, evec⟩ := xorValue_run (s := d) (k := klSlot)
    (by rw [hd5, hdw]; exact hscr) (by omega_arith)
  obtain ⟨ec, emk, et⟩ := tab_of evec
    (fun r hr => eg r (by revert r; decide) (by revert r; decide) (by revert r; decide)) dc dmk dt
  obtain ⟨f, fe, fh, fc, fmk, ft, fg, fm, frd, fwr⟩ :=
    pairConst_run e Spec.Camellia.sigma3 Spec.Camellia.sigma4 ec emk et
  obtain hf5 : f.gpr sb = s.gpr sb := by
    rw [fg _ (by decide), eg _ (by decide) (by decide) (by decide), hd5]
  obtain hfs : ∀ j, slotW f j = slotW s j := fun j => by
    rw [slotW_eq_of (fm.trans em) (by rw [hf5, hd5]), hds]
  obtain hfw : f.wr = s.wr := by rw [fwr, ewr, hdw]
  obtain hfh : halves f = kaD2 KL KR := by
    rw [fh, eh, hdh, hds, hds, rev_of_wordOf hkl.1, rev_of_wordOf hkl.2]; rfl
  obtain hfm : f.mem = s.mem := by rw [fm, em, dm, cm, bm, am]
  -- `KA` to its keySlots.
  obtain ⟨g, ge, gw, gk, gg, gf, grd, gwr, gvec⟩ := storeValue_run (s := f) (k := kaSlot)
    (by rw [hf5, hfw]; exact hscr) (by omega_arith)
  obtain ⟨gc, gmk, gt⟩ := tab_of gvec (fun r hr => gg r (by revert r; decide)) fc fmk ft
  refine ⟨g, ?_, ?_, by rw [← hfh]; exact gw, gc, gmk, gt,
    fun j hj h0 h1 => by rw [gk j hj h0 h1, hfs], fun r hr => ?_, ?_,
    by rw [grd, frd, erd, drd, crd, brd, ard], by rw [gwr, hfw]⟩
  · rw [ka, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append,
      VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append,
      ae, Option.bind_some, be, Option.bind_some, ce, Option.bind_some, de, Option.bind_some,
      ee, Option.bind_some, fe, Option.bind_some, ge]
  · rw [← hfh]; simp only [halves, gg _ (by decide : Reg.x6 ≠ .x8), gg _ (by decide : Reg.x7 ≠ .x8)]
  · obtain ⟨n6, n7, n8⟩ := nw hr
    rw [gg r n8, fg r hr, eg r n6 n7 n8, dg r hr, cg r n6 n7 n8, bg r n7, ag r n6]
  · rw [hf5, hfm] at gf; exact gf

/-- `kb`: `KB` in its keySlots, from `KA` in the halves. -/
theorem kb_run {s : State} {D KR : BitVec 64 × BitVec 64}
    (hscr : (⟨s.gpr sb, 8 * keySlots⟩ : Region) ∈ s.wr) (hc : Constants s) (hm : Masks s) (ht : Table s)
    (hd : halves s = D) (hkr : WordsAt s krSlot KR) :
    ∃ t, runBlock isa kb s = some t ∧
      WordsAt t kbSlot (pair Spec.Camellia.sigma5 Spec.Camellia.sigma6 (D.1 ^^^ KR.1, D.2 ^^^ KR.2)) ∧
      (∀ j < keySlots, j ≠ kbSlot → j ≠ kbSlot + 1 → slotW t j = slotW s j) ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧ Frame [⟨s.gpr sb, 8 * keySlots⟩] s.mem t.mem ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨hl, hr, -, hA, hB, -, -, hS⟩ := kaKb_slots
  obtain nw : ∀ {r : Reg}, r ∉ written → r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x8 := fun {r} h =>
    ⟨fun e => h (e ▸ by decide), fun e => h (e ▸ by decide), fun e => h (e ▸ by decide)⟩
  obtain ⟨c, ce, ch, cg, cm, crd, cwr, cvec⟩ := xorValue_run (s := s) (k := krSlot) hscr (by omega_arith)
  obtain ⟨cc, cmk, ct⟩ := tab_of cvec
    (fun r hr => cg r (by revert r; decide) (by revert r; decide) (by revert r; decide)) hc hm ht
  obtain ⟨d, de, dh, dc, dmk, dt, dg, dm, drd, dwr⟩ :=
    pairConst_run c Spec.Camellia.sigma5 Spec.Camellia.sigma6 cc cmk ct
  obtain hd5 : d.gpr sb = s.gpr sb := by rw [dg _ (by decide), cg _ (by decide) (by decide) (by decide)]
  obtain hds : ∀ j, slotW d j = slotW s j := slotW_eq_of (dm.trans cm) hd5
  obtain hdw : d.wr = s.wr := by rw [dwr, cwr]
  obtain hdh : halves d = pair Spec.Camellia.sigma5 Spec.Camellia.sigma6 (D.1 ^^^ KR.1, D.2 ^^^ KR.2) := by
    rw [dh, ch, hd, rev_of_wordOf hkr.1, rev_of_wordOf hkr.2]
  obtain ⟨g, ge, gw, gk, gg, gf, grd, gwr, -⟩ := storeValue_run (s := d) (k := kbSlot)
    (by rw [hd5, hdw]; exact hscr) (by omega_arith)
  refine ⟨g, ?_, by rw [← hdh]; exact gw, fun j hj h0 h1 => by rw [gk j hj h0 h1, hds],
    fun r hr => ?_, ?_, by rw [grd, drd, crd], by rw [gwr, hdw]⟩
  · rw [kb, VG.Interleave.runBlock_append, VG.Interleave.runBlock_append, ce, Option.bind_some, de,
      Option.bind_some, ge]
  · obtain ⟨n6, n7, n8⟩ := nw hr
    rw [gg r n8, dg r hr, cg r n6 n7 n8]
  · rw [hd5, show d.mem = s.mem from dm.trans cm] at gf; exact gf

/-! ## The subkeys -/

/-- The subkeys of a key of 16 bytes do not use `KB`. -/
theorem subkeyWords_128 (a b c d d' : BitVec 128) :
    Proof.Camellia.subkeyWords [a, b, c, d] Impl.Camellia.subkeys128 =
      Proof.Camellia.subkeyWords [a, b, c, d'] Impl.Camellia.subkeys128 := by
  unfold Proof.Camellia.subkeyWords
  refine List.map_congr_left fun k hk => ?_
  obtain h : k.1 = 0 ∨ k.1 = 2 := (by decide : ∀ k ∈ Impl.Camellia.subkeys128, k.1 = 0 ∨ k.1 = 2) k hk
  obtain ⟨v, r, hh⟩ := k
  rcases h with h | h <;> (simp only at h; subst h; rfl)

/-- What the subkeys' stores leave: the schedule's bytes. -/
structure StoresPost (s₈ : State) (S : Addr) (len : Nat) (key : List Byte) (s : State) : Prop where
  bytes : Spec.Camellia.bytesAt s.mem S (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
    Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key)
  frame : Frame [⟨S, 272⟩] s₈.mem s.mem
  base : s.gpr sb = s₈.gpr sb
  rd : s.rd = s₈.rd
  wr : s.wr = s₈.wr

/-- The values into registers, and the stores of one key length's subkeys. -/
theorem stores_wp {s₈ : State} {S : Addr} {len : Nat} {key : List Byte} {ks : List (Nat × Nat × Bool)}
    {vs : List (BitVec 128)} (hscr : (⟨s₈.gpr sb, 8 * keySlots⟩ : Region) ∈ s₈.wr)
    (hS : s₈.gpr .x2 = S) (hw : (⟨S, 272⟩ : Region) ∈ s₈.wr) (hv : ∀ k ∈ ks, k.1 < 4)
    (hks : ks.length ≤ 34)
    (hw4 : ∀ v < 4, WordsAt s₈ ([klSlot, krSlot, kaSlot, kbSlot].getD v 0) (hiW (vs.getD v 0), loW (vs.getD v 0)))
    (hlen : 8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len) = 8 * ks.length)
    (hks' : Proof.Camellia.subkeyWords vs ks = Spec.Camellia.scheduleWords (Spec.Camellia.expandKey key)) :
    WP isa (.block (loadValues ++ storeSubkeys ks)) s₈ (StoresPost s₈ S len key) := by
  obtain ⟨s₆, e₆, v₆, o₆, m₆, rd₆, wr₆⟩ := loadValues_ok (s := s₈) hscr vs hw4
  obtain hnv : ∀ r : Reg, r ∈ [sb, Reg.x2] → ∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v := by decide
  obtain hS₆ : s₆.gpr .x2 = S := by rw [o₆ _ (hnv _ (by simp)), hS]
  obtain ⟨s₉, e₉, b₉, f₉, g₉, rd₉, wr₉⟩ := storeSubkeys_ok ks hv 0 s₆ (fun i hi => ⟨_, by rw [wr₆]; exact hw, by
    rw [hS₆]; exact VG.Offset.contains_base _ (by omega_using [hks, hi]) (by omega_using [hks, hi])⟩) (by omega_using [hks])
  refine WP.of_runBlock ⟨s₉, by rw [runBlock_append', e₆, Option.bind_some]; exact e₉, ⟨?_, ?_, ?_,
    by rw [rd₉, rd₆], by rw [wr₉, wr₆]⟩⟩
  · rw [hlen, schedule_of_stores (vs := vs) (H := fun v => s₆.gpr (hiReg v)) (L := fun v => s₆.gpr (loReg v)) hv
      v₆ (by rw [← hS₆]; exact b₉), Spec.Camellia.scheduleBytes, hks']
  · rw [hS₆, m₆] at f₉
    exact f₉.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base S (by omega_using [hks])⟩
  · rw [g₉ _ (by decide) (by decide), o₆ _ (hnv _ (by simp))]

/-! ## The whole function -/

theorem expandKey_wp {s₀ : State} (hp : expandKeyAArch64.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      expandKeyAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hlen⟩ := hp
  obtain ⟨hl', hr', hT, hA, hB, hE, hK, hS⟩ := kaKb_slots
  have ht := klSlot_eq
  have hsv := ksavedSlot_eq
  obtain hwB : (⟨s₀.gpr .x3, 8 * keySlots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  obtain hwS : (⟨s₀.gpr .x2, 272⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  obtain hrK : (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  unfold expandKey
  -- The prologue.
  obtain ⟨s₁a, e₁a, r₁a, o₁a, m₁a, rd₁a, wr₁a⟩ := movR_ok s₀ sb .x3
  obtain ⟨s₁b, e₁b, r₁b, o₁b, m₁b, rd₁b, wr₁b⟩ := movR_ok s₁a .x3 .x1
  obtain hb₁b : s₁b.gpr sb = s₀.gpr .x3 := by rw [o₁b _ (by decide), r₁a]
  obtain g₁b : ∀ r, r ≠ sb → r ≠ .x3 → s₁b.gpr r = s₀.gpr r := fun r h1 h2 => by rw [o₁b r h2, o₁a r h1]
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁', wr₁', f₁', -⟩ := ksave_ok (b := s₀.gpr .x3) (by rw [wr₁b, wr₁a]; exact hwB) hb₁b
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [runBlock_append', show ([movR sb .x3, movR .x3 .x1] : List Instr) = [movR sb .x3] ++ [movR .x3 .x1] from rfl,
      runBlock_append', e₁a, Option.bind_some, e₁b, Option.bind_some, e₁], ?_⟩)
  obtain b₁ : s₁.gpr sb = s₀.gpr .x3 := by rw [g₁, hb₁b]
  obtain x3₁ : s₁.gpr .x3 = s₀.gpr .x1 := by rw [g₁, r₁b, o₁a _ (by decide)]
  obtain x0₁ : s₁.gpr .x0 = s₀.gpr .x0 := by rw [g₁, g₁b _ (by decide) (by decide)]
  obtain x2₁ : s₁.gpr .x2 = s₀.gpr .x2 := by rw [g₁, g₁b _ (by decide) (by decide)]
  obtain rd₁ : s₁.rd = s₀.rd := by rw [rd₁', rd₁b, rd₁a]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [wr₁', wr₁b, wr₁a]
  obtain sv₁' : KSaved s₀ (s₀.gpr .x3) s₁.mem := fun i hi => by
    obtain n := sreg_ne' i hi
    rw [sv₁ i hi, g₁b _ n.1 n.2]
  obtain f₁ : Frame [⟨s₀.gpr .x3, 8 * klSlot⟩] s₀.mem s₁.mem := by
    have := f₁'.sub (rs' := [⟨s₀.gpr .x3, 8 * klSlot⟩]) fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base _ (by omega_arith)⟩
    rw [m₁b, m₁a] at this; exact this
  -- The key, unchanged so far.
  obtain hkey₁ : Spec.Camellia.bytesAt s₁.mem (s₁.gpr .x0) (s₀.gpr .x1).toNat =
      Spec.Camellia.bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat := by
    rw [x0₁]
    refine Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩)
      (fun r hr => ?_) (by simp only; omega_using []) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact dKB.sub_right (Region.sub_prefix (by omega_using [hS, ht]))
  -- `KL` and `KR`.
  refine WP.seq (WP.mono (loadKey_wp (len := (s₀.gpr .x1).toNat) (s := s₁) (by rw [b₁, wr₁]; exact hwB)
    (by rw [x0₁, rd₁]; exact hrK) (by rw [x0₁]; exact fitK) (by rw [x0₁, b₁]; exact dKB)
    (by rw [x3₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hlen) fun s₂ h₂ => ?_)
  obtain ⟨kl₂, kr₂, sl₂, g₂, f₂, rd₂, wr₂⟩ := h₂
  rw [hkey₁] at kl₂ kr₂
  generalize hkey : Spec.Camellia.bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat = key at kl₂ kr₂
  obtain hb₂ : s₂.gpr sb = s₀.gpr .x3 := by rw [g₂ _ (by decide) (by decide) (by decide), b₁]
  obtain x2₂ : s₂.gpr .x2 = s₀.gpr .x2 := by rw [g₂ _ (by decide) (by decide) (by decide), x2₁]
  obtain x3₂ : s₂.gpr .x3 = s₀.gpr .x1 := by rw [g₂ _ (by decide) (by decide) (by decide), x3₁]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, wr₁]
  let KL : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).1, loW (Spec.Camellia.klkr key).1)
  let KR : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).2, loW (Spec.Camellia.klkr key).2)
  -- The key's length, the table and the masks, and `KA`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₃, e₃, z₃, g₃, m₃, rd₃, wr₃⟩ := subI_ok s₂ t0 .x3 (imm := 16) (by decide)
  refine WP.of_runBlock ⟨s₃, e₃, ?_⟩
  refine WP.mono (VG.AArch64.Tbl.loadTable_ok s₃ _) fun s₄ ⟨tb₄, v₄, g₄, m₄, rd₄, wr₄, _⟩ => ?_
  obtain ⟨s₅, e₅, c₅, g₅, m₅, rd₅, wr₅, -, v₅⟩ := Serial.quarterConstants_run s₄
  refine WP.of_runBlock ⟨s₅, e₅, ?_⟩
  obtain ⟨s₆, e₆, mk₆, g₆, m₆, rd₆, wr₆, -, v₆⟩ := Serial.maskConstants_run s₅
  refine WP.of_runBlock ⟨s₆, e₆, ?_⟩
  obtain c₆ : Constants s₆ := by simpa only [Constants, v₆] using c₅
  obtain t₆ : Table s₆ := fun j hj => by
    rw [v₆, VG.AArch64.Tbl.tbyte_congr' (fun i hi => by
      obtain hn := VG.AArch64.Tbl.treg_ne8 i hi
      exact v₅ _ hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2.1) j hj]
    exact tb₄ j hj
  obtain g₆' : ∀ r, r ∉ [t0, .x6, .x7] → r ∉ Serial.maskRegs → s₆.gpr r = s₂.gpr r := fun r hr hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₆ r hm, g₅ r (fun h => hm (by rw [h]; decide)), g₄ r hr.2.1 hr.2.2, g₃ r hr.1]
  obtain hb₆ : s₆.gpr sb = s₀.gpr .x3 := by rw [g₆' _ (by decide) (by decide), hb₂]
  obtain m₆' : s₆.mem = s₂.mem := by rw [m₆, m₅, m₄, m₃]
  obtain wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃, wr₂']
  obtain hs₆ : ∀ k, slotW s₆ k = slotW s₂ k := slotW_eq_of m₆' (by rw [hb₆, hb₂])
  obtain ⟨s₇, e₇, h₇, ka₇, c₇, mk₇, t₇, sl₇, g₇, f₇, rd₇, wr₇⟩ := ka_run (s := s₆) (KL := KL) (KR := KR)
    (by rw [hb₆, wr₆']; exact hwB) c₆ mk₆ t₆ (kl₂.congr (hs₆ _) (hs₆ _)) (kr₂.congr (hs₆ _) (hs₆ _))
  refine WP.of_runBlock ⟨s₇, e₇, ?_⟩
  obtain hb₇ : s₇.gpr sb = s₀.gpr .x3 := by rw [g₇ _ (by decide), hb₆]
  obtain wr₇' : s₇.wr = s₀.wr := by rw [wr₇, wr₆']
  obtain hscr₇ : (⟨s₇.gpr sb, 8 * keySlots⟩ : Region) ∈ s₇.wr := by rw [hb₇, wr₇']; exact hwB
  obtain x2₇ : s₇.gpr .x2 = s₀.gpr .x2 := by rw [g₇ _ (by decide), g₆' _ (by decide) (by decide), x2₂]
  obtain hz₇ : (s₇.gpr t0 == 0) = decide ((s₀.gpr .x1).toNat = 16) := by
    rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide),
      g₄ _ (by decide) (by decide), z₃, x3₂]
    conv => lhs; rw [show s₀.gpr .x1 = BitVec.ofNat 64 (s₀.gpr .x1).toNat by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [VG.Offset.ofNat_sub_ofNat_beq (by omega_using []) (by decide)]
  -- The keySlots of `KL`, `KR` and the saved registers after `KA`.
  obtain hs₇ : ∀ k < keySlots, k ≠ kaSlot → k ≠ kaSlot + 1 → slotW s₇ k = slotW s₂ k := fun k hk h0 h1 => by
    rw [sl₇ k hk h0 h1, hs₆]
  obtain kl₇ : WordsAt s₇ klSlot KL := kl₂.congr (hs₇ _ (by omega_arith) (by omega_arith) (by omega_arith))
    (hs₇ _ (by omega_arith) (by omega_arith) (by omega_arith))
  obtain kr₇ : WordsAt s₇ krSlot KR := kr₂.congr (hs₇ _ (by omega_arith) (by omega_arith) (by omega_arith))
    (hs₇ _ (by omega_arith) (by omega_arith) (by omega_arith))
  obtain ⟨hKA, hKB⟩ := kaD_eq (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2
  have hKA' : kaD2 KL KR = _ := hKA
  have hKB' : kaD3 KL KR = _ := hKB
  obtain hklen : key.length = (s₀.gpr .x1).toNat := by rw [← hkey]; simp [Spec.Camellia.bytesAt]
  obtain hsv₇ : ∀ k, ksavedSlot ≤ k → k < ksavedSlot + 10 → slotW s₇ k = slotW s₁ k := fun k h1 h2 => by
    rw [hs₇ k (by omega_arith) (by omega_arith) (by omega_arith),
      sl₂ k (by omega_arith) (Or.inl (by omega_arith))]
  -- The subkeys.
  refine WP.seq (WP.mono (Q := fun (s₉ : State) => Spec.Camellia.bytesAt s₉.mem (s₀.gpr .x2)
        (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds (s₀.gpr .x1).toNat)) =
        Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key) ∧ s₉.gpr sb = s₀.gpr .x3 ∧
      s₉.wr = s₀.wr ∧ ∀ k, ksavedSlot ≤ k → k < ksavedSlot + 10 → slotW s₉ k = slotW s₁ k)
    (WP.ite (decide ((s₀.gpr .x1).toNat = 16)) ((eval_zero s₇ t0).trans (by rw [hz₇])) (fun h16 => ?_)
      (fun h16 => ?_))
    fun s₉ h₉ => ?_)
  · -- A key of 16 bytes: `KB`'s keySlots hold what they held.
    obtain h16 : (s₀.gpr .x1).toNat = 16 := by simpa using h16
    obtain kb₇ : WordsAt s₇ kbSlot (hiW (rev64 (slotW s₇ kbSlot) ++ rev64 (slotW s₇ (kbSlot + 1))),
        loW (rev64 (slotW s₇ kbSlot) ++ rev64 (slotW s₇ (kbSlot + 1)))) := by
      rw [Proof.Camellia.hiW_append, Proof.Camellia.loW_append]
      exact ⟨wordOf_self_rev _, wordOf_self_rev _⟩
    refine WP.mono (stores_wp (len := (s₀.gpr .x1).toNat) (key := key)
      (vs := [(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        rev64 (slotW s₇ kbSlot) ++ rev64 (slotW s₇ (kbSlot + 1))]) hscr₇ x2₇
      (by rw [wr₇']; exact hwS) subkeys_lt4.1 (by rw [subkeys_length.1]; omega_using [])
      (fun v hv => by
        rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_using [hv]) with rfl | rfl | rfl | rfl
        · exact kl₇
        · exact kr₇
        · have := ka₇; rw [hKA'] at this; exact this
        · exact kb₇)
      (by rw [h16, subkeys_length.1]; rfl)
      (by rw [Proof.Camellia.scheduleWords_expandKey, hklen, ite_eq_left h16]; exact subkeyWords_128 _ _ _ _ _))
      fun s₉ h₉ => ⟨h₉.bytes, h₉.base.trans hb₇, h₉.wr.trans wr₇', fun k h1 h2 => ?_⟩
    rw [← hsv₇ k h1 h2]
    simp only [slotW, h₉.base]
    exact h₉.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hb₇]
      exact (dSB.sub_right (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega_arith))).symm) (by decide)
  · -- A key of 24 or 32 bytes: `KB`.
    obtain h16 : (s₀.gpr .x1).toNat ≠ 16 := by simpa using h16
    rw [WP.block_append_iff]
    obtain ⟨s₈, e₈, kb₈, sl₈, g₈, f₈, rd₈, wr₈⟩ := kb_run (s := s₇) (D := kaD2 KL KR) (KR := KR) hscr₇ c₇ mk₇ t₇
      h₇ kr₇
    refine WP.of_runBlock ⟨s₈, e₈, ?_⟩
    obtain hb₈ : s₈.gpr sb = s₇.gpr sb := g₈ _ (by decide)
    obtain wr₈' : s₈.wr = s₀.wr := by rw [wr₈, wr₇']
    have hs₈ : ∀ k < keySlots, k ≠ kbSlot → k ≠ kbSlot + 1 → slotW s₈ k = slotW s₇ k := sl₈
    refine WP.mono (stores_wp (len := (s₀.gpr .x1).toNat) (key := key)
      (vs := [(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2])
      (by rw [hb₈, wr₈, wr₇]; rw [wr₇] at hscr₇; exact hscr₇) (by rw [g₈ _ (by decide), x2₇])
      (by rw [wr₈']; exact hwS) subkeys_lt4.2 (by rw [subkeys_length.2])
      (fun v hv => by
        rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega_using [hv]) with rfl | rfl | rfl | rfl
        · exact kl₇.congr (hs₈ _ (by omega_arith) (by omega_arith) (by omega_arith))
            (hs₈ _ (by omega_arith) (by omega_arith) (by omega_arith))
        · exact kr₇.congr (hs₈ _ (by omega_arith) (by omega_arith) (by omega_arith))
            (hs₈ _ (by omega_arith) (by omega_arith) (by omega_arith))
        · have := ka₇.congr (hs₈ _ (by omega_arith) (by omega_arith) (by omega_arith))
            (hs₈ _ (by omega_arith) (by omega_arith) (by omega_arith))
          rw [hKA'] at this; exact this
        · have := kb₈; rw [show pair Spec.Camellia.sigma5 Spec.Camellia.sigma6
            ((kaD2 KL KR).1 ^^^ KR.1, (kaD2 KL KR).2 ^^^ KR.2) = kaD3 KL KR from rfl, hKB'] at this
          exact this)
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [Proof.Camellia.scheduleWords_expandKey, hklen, ite_eq_right h16]))
      fun s₉ h₉ => ⟨h₉.bytes, h₉.base.trans (hb₈.trans hb₇), h₉.wr.trans wr₈', fun k h1 h2 => ?_⟩
    rw [← hsv₇ k h1 h2, ← hs₈ k (by omega_arith) (by omega_arith) (by omega_arith)]
    simp only [slotW, h₉.base]
    exact h₉.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hb₈, hb₇]
      exact (dSB.sub_right (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega_arith))).symm) (by decide)
  -- The epilogue.
  obtain ⟨by₉, hb₉, wr₉, sv₉⟩ := h₉
  obtain ⟨s₁₀, e₁₀, rg₁₀, -, m₁₀, -, -⟩ := krestore_ok (s₀ := s₀) (b := s₀.gpr .x3)
    (by rw [wr₉]; exact hwB) hb₉ (fun i hi => by
      have := sv₉ (ksavedSlot + i) (by omega_using []) (by omega_using [hi])
      simp only [slotW, hb₉, b₁] at this
      rw [this]; exact sv₁' i hi)
  refine WP.of_runBlock ⟨s₁₀, e₁₀, rg₁₀, ?_⟩
  show Spec.Camellia.bytesAt s₁₀.mem (s₀.gpr .x2) _ = _
  rw [hkey, m₁₀, ← by₉]

theorem expandKey_correct (s : State) (hs : expandKeyAArch64.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyAArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (expandKey_wp hs) (by lit_decide)
    (by lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
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
  · exact h₃ _ (by simp)

/-- A state satisfying the precondition (a key of 16 bytes). -/
def expandKeySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 272⟩, ⟨0x4000, 8 * 20⟩]

theorem expandKey_verified :
    Verified AArch64.target expandKey (Proof.Camellia.expandKeyScratchContract AArch64.abi keySlots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Camellia.expandKeyScratchContract, Proof.Camellia.expandKeyScratchSig,
      Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre, Spec.Camellia.expandKeyPost, expandKeyAArch64,
      AArch64.abi, AArch64.argRegs, keySlots, klSlot, ksavedSlot, endSlot, keySlot] [expandKeySat]
      using expandKeySat)

/-- A state satisfying the key schedule's precondition: a key of 16 bytes at
`0x1000`, the schedule at `0x3000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x3000, 272⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Camellia.expandKeyContract AArch64.abi 160).pre s := by
  implies_sat [Spec.Camellia.expandKeyContract, Spec.Camellia.expandKeySig, Spec.Camellia.expandKeyPre,
    Spec.Camellia.expandKeyPost, AArch64.abi, AArch64.argRegs] [expandKeyFrameSat] using expandKeyFrameSat

/-- The key schedule, with its working space on the stack. -/
theorem expandKey_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 160 .x3 20 expandKey)
      (Spec.Camellia.expandKeyContract AArch64.abi 160) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 20) (pre := Spec.Camellia.expandKeyPre AArch64.abi.ptrBits)
    (post := Spec.Camellia.expandKeyPost AArch64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 160) (by rw [← Proof.Camellia.expandKeyScratchContract_eq]; exact expandKey_verified)
    (by decide) (by decide) (by decide) (Proof.Camellia.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Camellia.AArch64
