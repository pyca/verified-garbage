module

import VerifiedGarbage.Proof.Camellia.X86.Fl
public import VerifiedGarbage.Proof.Camellia.Words
public import VerifiedGarbage.Proof.Camellia.X86.Round
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Eight blocks of bitsliced Camellia on x86 (32-bit): the rounds

As on ARMv7 (`Proof/Camellia/Arm/Core.lean`): with the table of bitsliced
subkeys `E 0 … E (8 g + 1)` in the scratch buffer (`CorePre`), the groups
of rounds of `crypt8` take the halves in their slots through `groups g E`.
They write only the slots below the table and the slot of the group's end
(`Ctx`). The rounds are `round_ok`, FL and FLINV `fl_ok` and `flinv_ok`;
the pairs of rounds and the groups of six are loops around them, whose
invariants are the specification's `pair` and `group`
(`Proof/Camellia/Words.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb tmpRegs movR movS addI subR movI subI slotAt st)
open VG.Proof.Camellia (pair group groups cryptWords pairsN pairsN_succ group_eq)

theorem slots_eq : slots = 672 := rfl
theorem tailSlot_eq : tailSlot = 72 := rfl
theorem keySlot_eq : keySlot = 104 := rfl
theorem grpSlot_eq : grpSlot = 654 := rfl
theorem savedSlot_eq : savedSlot = 648 := rfl
theorem dSlot_eq : dSlot = 652 := rfl
theorem nSlot_eq : nSlot = 653 := rfl
theorem d1Slot_eq : d1Slot = 40 := rfl
theorem d2Slot_eq : d2Slot = 56 := rfl

/-- Word `j` of entry `i` of the table, in the scratch buffer at `b`. -/
def entryW (m : Mem) (b : BitVec 32) (i j : Nat) : BitVec 32 := m.readW (wordAddr b (keySlot + 16 * i + j)) 32

/-- The scratch buffer at `b`, of `slots` slots or more (a mode keeps its
own after them), in the regions `rs`. -/
structure ScrIn (rs : List Region) (b : BitVec 32) : Prop where
  mem : ∃ n, slots ≤ n ∧ b.toNat + 4 * n ≤ 2 ^ 32 ∧ (⟨b.setWidth 64, 4 * n⟩ : Region) ∈ rs
  fit : b.toNat + 4 * slots ≤ 2 ^ 32

/-- What the rounds need: the scratch buffer, writable, and a table of `nk`
subkeys. -/
structure KeyCtx (s₀ : State) (nk : Nat) (E : Nat → BitVec 64) : Prop where
  scr : ScrIn s₀.wr (s₀.gpr sb)
  nk34 : nk ≤ 34
  keys : ∀ i < nk, W32.HalfRel (entryW s₀.mem (s₀.gpr sb) i) fun _ => E i

/-- What the groups of rounds need: the table of `8 g + 2` subkeys. -/
structure CorePre (s₀ : State) (g : Nat) (E : Nat → BitVec 64) : Prop extends KeyCtx s₀ (8 * g + 2) E where
  hg : g = 3 ∨ g = 4

/-- What the rounds may write in the scratch buffer at `b`: the slots below
the table, and the slot of the group's end. -/
def ctxRegions (b : BitVec 32) : List Region :=
  [⟨b.setWidth 64, 4 * keySlot⟩, ⟨wordAddr b grpSlot, 4⟩]

/-- What stays the same: the regions, the registers but the layers' and
`kp`, and the memory outside `ctxRegions`. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ tmpRegs → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame (ctxRegions (s₀.gpr sb)) s₀.mem s.mem

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide)

/-- A step that writes only the layers' registers, `kp`, and the regions. -/
theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ tmpRegs → r ≠ kp → s'.gpr r = s.gpr r)
    (hf : Frame (ctxRegions (s₀.gpr sb)) s.mem s'.mem) : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 => (hk r h1 h2).trans (hc.keep r h1 h2), hc.frame.trans hf⟩

/-- A step that writes only the slots below the tail buffer. -/
theorem Ctx.stepL {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ tmpRegs → r ≠ kp → s'.gpr r = s.gpr r)
    (hf : Frame [slotRegion layerCfg s] s.mem s'.mem) : Ctx s₀ s' :=
  hc.step hrd hwr hk (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., by
      simp only [slotRegion, layerCfg, hc.base]; exact Region.sub_prefix (by simp [tailSlot, keySlot])⟩)

/-- A step that changes only `kp` and `eax` (and the flags). -/
theorem Ctx.regs {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ kp → r ≠ .eax → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r h1 h2 => hg r h2 fun h => h1 (by subst h; decide)) (by rw [hm]; exact Frame.refl _ _)

/-! ## Addresses -/

theorem setWidth_toNat (b : BitVec 32) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- Slot `k` of the scratch buffer at `b`, as a 64-bit offset. -/
theorem slot_addr {b : BitVec 32} {k : Nat} (hfit : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    wordAddr b k = b.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega)

/-- Slot `k` is in the scratch buffer. -/
theorem slot_in {rs : List Region} {b : BitVec 32} {n k : Nat} (hr : (⟨b.setWidth 64, 4 * n⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) : InRegions rs (wordAddr b k) 4 :=
  ⟨_, hr, by
    rw [slot_addr (by omega)]
    have := setWidth_toNat b
    exact VG.Offset.contains_base _ (by omega) (by omega)⟩

/-- A scratch buffer of exactly `slots` slots. -/
theorem ScrIn.exact {rs : List Region} {b : BitVec 32} (hr : (⟨b.setWidth 64, 4 * slots⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) : ScrIn rs b := ⟨⟨slots, Nat.le_refl _, hfit, hr⟩, hfit⟩

theorem ScrIn.slot {rs : List Region} {b : BitVec 32} (h : ScrIn rs b) {k : Nat} (hk : k < slots) :
    InRegions rs (wordAddr b k) 4 :=
  let ⟨_, hn, hf, hr⟩ := h.mem
  slot_in hr hf (Nat.lt_of_lt_of_le hk hn)

theorem ScrIn.slot_rd {s : State} {b : BitVec 32} (h : ScrIn s.wr b) {k : Nat} (hk : k < slots) :
    InRegions (s.rd ++ s.wr) (wordAddr b k) 4 := by
  obtain ⟨r, hr, hc⟩ := h.slot hk
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- `kp` at entry `m` of the table. -/
def AtEntry (s : State) (b : BitVec 32) (m : Nat) : Prop := s.gpr kp = b + BitVec.ofNat 32 (4 * keySlot + 64 * m)

theorem wordAddr_entry {s : State} {b : BitVec 32} {m : Nat} (hk : AtEntry s b m) (j : Nat) :
    wordAddr (s.gpr kp) j = wordAddr b (keySlot + 16 * m + j) := by
  simp only [wordAddr, addr]
  rw [show s.gpr kp = _ from hk, VG.Offset.add_add,
    show 4 * keySlot + 64 * m + 4 * j = 4 * (keySlot + 16 * m + j) by omega]

theorem keyW_entry {s : State} {b : BitVec 32} {m : Nat} (hk : AtEntry s b m) (e j : Nat) :
    keyW s (16 * e + j) = entryW s.mem b (m + e) j := by
  simp only [keyW, entryW, wordAddr_entry hk,
    show keySlot + 16 * m + (16 * e + j) = keySlot + 16 * (m + e) + j by omega]

theorem ok_layer {s : State} {b : BitVec 32} {m : Nat} (hscr : ScrIn s.wr b) (hb : s.gpr sb = b)
    (hk : AtEntry s b m) (hm : m + 2 ≤ 34) : Ok layerCfg s where
  slotIn k hk' := by
    simp only [layerCfg, tailSlot_eq] at hk' ⊢
    rw [hb]; exact hscr.slot (by rw [slots_eq]; omega)
  extIn j hj := by
    simp only [layerCfg] at hj ⊢
    rw [wordAddr_entry hk]
    exact hscr.slot_rd (by rw [slots_eq, keySlot_eq]; omega)
  fit := by have := hscr.fit; simp only [layerCfg, tailSlot_eq]; rw [hb]; rw [slots_eq] at this; omega
  sep k hk' j hj := by
    have := hscr.fit
    simp only [layerCfg, tailSlot_eq] at hk' hj ⊢
    rw [wordAddr_entry hk, hb]
    rw [slots_eq] at this
    exact slot_sep b (by omega) (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)

/-- Slots outside `ctxRegions` are kept. -/
theorem Ctx.slot {s₀ s : State} (hc : Ctx s₀ s) (hfit : (s₀.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) {k : Nat}
    (hk : k < slots) (h1 : keySlot ≤ k) (h2 : k ≠ grpSlot) : slotW s k = slotW s₀ k := by
  simp only [slotW, hc.base]
  rw [slots_eq] at hfit hk
  have hb := setWidth_toNat (s₀.gpr sb)
  rw [slot_addr (by omega)]
  refine hc.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base _ (by rw [keySlot_eq] at h1 ⊢; omega) (by omega)
  · rw [slot_addr (by rw [grpSlot_eq]; omega)]
    rw [grpSlot_eq] at h2 ⊢
    exact VG.Offset.disjoint _ (by omega) (by omega) (by omega)

theorem Ctx.entry {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {i j : Nat} (hi : i < 34) (hj : j < 16) :
    entryW s.mem (s₀.gpr sb) i j = entryW s₀.mem (s₀.gpr sb) i j := by
  have := hc.slot hp.scr.fit (k := keySlot + 16 * i + j) (by rw [slots_eq, keySlot_eq]; omega)
    (by omega) (by rw [grpSlot_eq, keySlot_eq]; omega)
  simp only [slotW, hc.base] at this
  exact this

theorem Ctx.keyRel {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m e : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hme : m + e < nk) :
    W32.HalfRel (fun j => keyW s (16 * e + j)) fun _ => E (m + e) := by
  have hg := hp.nk34
  refine (hp.keys _ hme).congr fun j hj => ?_
  rw [keyW_entry hk, hc.entry hp (by omega) hj]

theorem Ctx.ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 2 ≤ 34) : Ok layerCfg s :=
  ok_layer (by rw [hc.wr]; exact hp.scr) hc.base hk hm

theorem Ctx.scr {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    ScrIn s.wr (s.gpr sb) := ⟨by rw [hc.wr, hc.base]; exact hp.scr.mem, by rw [hc.base]; exact hp.scr.fit⟩

/-! ## Single instructions -/

/-- `add d, v`. -/
theorem addI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [addI d v] s = some s' ∧ s'.gpr d = s.gpr d + v ∧
      s'.zf = some (s.gpr d + v == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨(arithFlags s (s.gpr d + v) (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat) (addOverflow (s.gpr d) v (s.gpr d + v))).setReg d
      (s.gpr d + v), rfl, RegUpd.gpr_setReg_self _ _ _, rfl, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩

/-- `sub d, v`. -/
theorem subI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [subI d v] s = some s' ∧ s'.gpr d = s.gpr d - v ∧
      s'.zf = some (s.gpr d - v == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨(arithFlags s (s.gpr d - v) ((s.gpr d).toNat < v.toNat) (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d
      (s.gpr d - v), rfl, RegUpd.gpr_setReg_self _ _ _, rfl, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩

/-- `mov d, s`. -/
theorem movR_ok (s : State) (d r₀ : Reg) :
    ∃ s', runBlock isa [movR d r₀] s = some s' ∧ s'.gpr d = s.gpr r₀ ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf ∧
      s'.cf = s.cf :=
  ⟨s.setReg d (s.gpr r₀), rfl, RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl, rfl, rfl⟩

/-- `mov d, v`. -/
theorem movI_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [movI d v] s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d v, rfl, RegUpd.gpr_setReg_self _ _ _, fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr,
    rfl, rfl, rfl⟩

/-- `mov eax, kp; sub eax, edi; cmp eax, v`. -/
theorem endTest_ok (s : State) (v : BitVec 32) :
    ∃ s', runBlock isa [movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm v)] s = some s' ∧
      s'.zf = some (s.gpr kp - s.gpr .edi - v == 0) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := movR_ok s .eax kp
  obtain ⟨s₂, e₂, r₂, -, o₂, m₂, rd₂, wr₂⟩ := subI_ok s₁ .eax (s₁.gpr .edi)
  let s₃ := arithFlags s₂ (s₂.gpr .eax - v) ((s₂.gpr .eax).toNat < v.toNat) (subOverflow (s₂.gpr .eax) v (s₂.gpr .eax - v))
  refine ⟨s₃, ?_, ?_, fun r hr => by rw [RegUpd.gpr_arithFlags, o₂ r hr, o₁ r hr], by rw [RegUpd.mem_arithFlags, m₂, m₁],
    by rw [RegUpd.rd_arithFlags, rd₂, rd₁], by rw [RegUpd.wr_arithFlags, wr₂, wr₁]⟩
  · rw [show ([movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm v)] : List Instr) =
      [movR .eax kp] ++ ([subR .eax .edi] ++ [.alu .cmp .eax (.imm v)]) from rfl, runBlock_app, e₁, Option.bind_some,
      runBlock_app, show runBlock isa [subR .eax .edi] s₁ = runBlock isa [subI .eax (s₁.gpr .edi)] s₁ from rfl,
      e₂, Option.bind_some]
    rfl
  · rw [RegUpd.zf_arithFlags, r₂, r₁, o₁ _ (by decide)]

/-- `mov eax, [edi + 4 k]; cmp eax, kp`. -/
theorem cmpSlot_ok {s : State} (hs : ScrIn s.wr (s.gpr sb)) {k : Nat} (hk : k < slots) :
    ∃ s', runBlock isa [movS .eax k, .alu .cmp .eax (.reg kp)] s = some s' ∧
      s'.zf = some (slotW s k - s.gpr kp == 0) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr sb) k) 4 := hs.slot_rd hk
  let s₁ := s.setReg .eax (slotW s k)
  have e₁ : exec (movS .eax k) s = some s₁ := by
    show (s.load32 (wordAddr (s.gpr sb) k)).map (s.setReg .eax) = _
    simp only [State.load32, hin, ↓reduceIte, Option.map_some]
    rfl
  let a := s₁.gpr .eax
  let b := s₁.gpr kp
  refine ⟨arithFlags s₁ (a - b) (a.toNat < b.toNat) (subOverflow a b (a - b)), ?_, ?_,
    fun r hr => by rw [RegUpd.gpr_arithFlags]; exact RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons]
    rfl
  · rw [RegUpd.zf_arithFlags, show a = slotW s k from RegUpd.gpr_setReg_self _ _ _,
      show b = s.gpr kp from RegUpd.gpr_setReg_of_ne _ _ (by decide)]

theorem ofNat32_sub_beq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 32 x - BitVec.ofNat 32 y == 0) = decide (x = y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

theorem entry_beq (b : BitVec 32) {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (b + BitVec.ofNat 32 x - (b + BitVec.ofNat 32 y) == 0) = decide (x = y) := by
  rw [VG.Offset.add_sub_add_left, ofNat32_sub_beq hx hy]

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl
theorem eval_e (s : State) : isa.eval .e s = s.zf := rfl
theorem eval_b (s : State) : isa.eval .b s = s.cf := rfl

/-- `kp` stepped by `n` entries. -/
theorem AtEntry.add {s s' : State} {b : BitVec 32} {m n : Nat} (hk : AtEntry s b m)
    (h : s'.gpr kp = s.gpr kp + BitVec.ofNat 32 (64 * n)) : AtEntry s' b (m + n) := by
  rw [AtEntry, h, show s.gpr kp = _ from hk, VG.Offset.add_add]; congr 2; omega

/-! ## Rounds -/

/-- The halves of the eight blocks, `(D1, D2)` of block `b` in `S b`, in their slots. -/
def Halves (s : State) (S : Nat → BitVec 64 × BitVec 64) : Prop :=
  W32.HalfRel (half s d1Slot) (fun b => (S b).1) ∧ W32.HalfRel (half s d2Slot) (fun b => (S b).2)

theorem Halves.congr {s s' : State} {S : Nat → BitVec 64 × BitVec 64} (h : Halves s S)
    (hs : ∀ k, d1Slot ≤ k → k < tailSlot → slotW s' k = slotW s k) : Halves s' S :=
  ⟨h.1.congr fun i hi => hs _ (by omega) (by rw [d1Slot_eq, tailSlot_eq] at *; omega),
   h.2.congr fun i hi => hs _ (by rw [d1Slot_eq, d2Slot_eq]; omega) (by rw [d2Slot_eq, tailSlot_eq]; omega)⟩

/-- A frame of the slots below the tail buffer keeps the slots from the tail buffer on. -/
theorem slot_above_frame {s s' : State} (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32)
    (hb : s'.gpr sb = s.gpr sb) (hf : Frame [slotRegion layerCfg s] s.mem s'.mem) {k : Nat}
    (h1 : tailSlot ≤ k) (h2 : k < slots) : slotW s' k = slotW s k := by
  simp only [slotW, hb]
  exact slot_above (n := tailSlot) (by simpa [slotRegion, layerCfg] using hf) h1
    (by rw [slots_eq] at hfit h2; omega)

/-- A round, under `Ctx`, with the subkey at entry `m + off / 16`. -/
theorem round_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {off src dst m : Nat}
    (hA : check (lanes 32 11) layerCfg (linExt 32) (preL off src) (linEnv (halvesIns 0))
      (linPost tailSlot 11 (preOuts off src)) = true)
    (hC : check (lanes 32 12) layerCfg (linExt 40) (midLR off src) (linEnv midIns)
      (linPost tailSlot 12 (midOuts off src)) = true)
    (hE : check (lanes 32 11) linCfg (linExt 48) (postP dst) (linEnv postIns)
      (linPost tailSlot 11 (postOuts dst)) = true)
    (hall : ([Reg.esp, .esi, .edi].all fun r =>
      (preL off src ++ midLR off src ++ postP dst).all fun i => i.dst != some r) = true)
    (hcase : RoundCase off src dst)
    (hk : AtEntry s (s₀.gpr sb) m) (hme : m + off / 16 < nk) (hm34 : m + 2 ≤ 34)
    {X Y : Nat → BitVec 64} (hQ : W32.HalfRel (half s src) X) (hR : W32.HalfRel (half s dst) Y) :
    ∃ s', runBlock isa (round off src dst) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      W32.HalfRel (half s' dst) (fun b => Y b ^^^ Spec.Camellia.f (X b) (E (m + off / 16))) ∧
      (∀ i < 16, slotW s' (src + i) = slotW s (src + i)) ∧
      (∀ k, tailSlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hK : W32.HalfRel (fun j => keyW s (off + j)) fun _ => E (m + off / 16) := by
    have := hc.keyRel hp hk (e := off / 16) hme
    rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact this
  have hok := hc.ok hp hk hm34
  obtain ⟨s', h', hD, hsrc, rd', wr', o', f'⟩ := round_ok hA hC hE hall hcase hok hQ hK hR
  refine ⟨s', h', hc.stepL rd' wr' (fun r h1 _ => o' r h1) f', o' _ (by decide), hD, hsrc, fun k h1 h2 => ?_⟩
  exact slot_above_frame (by rw [hc.base]; exact hp.scr.fit) (o' _ (by decide)) f' h1 h2

/-- The two rounds of a pair, `kp += 128` and the comparison of `kp` with the
group's end. -/
theorem pair_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa pairBody s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      Halves s' (fun b => pair (E m) (E (m + 1)) (S b)) ∧
      s'.zf = some (slotW s grpSlot - s'.gpr kp == 0) ∧
      (∀ k, tailSlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  obtain ⟨h1, h2⟩ := hS
  obtain ⟨s₁, e₁, c₁, k₁, d₁, o₁, a₁⟩ := round_step hp hc (off := 0) (src := d1Slot) (dst := d2Slot)
    preL0_check mid0_check post2_check (by decide +kernel) (.inl ⟨rfl, rfl, rfl⟩) hk (by omega) hm34 h1 h2
  have hk₁ : AtEntry s₁ (s₀.gpr sb) m := by rw [AtEntry, k₁]; exact hk
  have h1' : W32.HalfRel (half s₁ d1Slot) (fun b => (S b).1) := h1.congr fun i hi => o₁ i hi
  obtain ⟨s₂, e₂, c₂, k₂, d₂, o₂, a₂⟩ := round_step hp c₁ (off := 16) (src := d2Slot) (dst := d1Slot)
    preL16_check mid16_check post1_check (by decide +kernel) (.inr ⟨rfl, rfl, rfl⟩) hk₁ (by omega) hm34 d₁ h1'
  have d₂' : W32.HalfRel (half s₂ d2Slot) (fun b => (S b).2 ^^^ Spec.Camellia.f (S b).1 (E (m + 0 / 16))) :=
    d₁.congr fun i hi => o₂ i hi
  obtain ⟨s₃, e₃, kp₃, -, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ kp 128
  have c₃ : Ctx s₀ s₃ := c₂.regs (fun r h _ => o₃ r h) m₃ rd₃ wr₃
  obtain ⟨s₄, e₄, z₄, o₄, m₄, rd₄, wr₄⟩ := cmpSlot_ok (c₃.scr hp) (k := grpSlot) (by rw [grpSlot_eq, slots_eq]; decide)
  have hs₄ : ∀ k, slotW s₄ k = slotW s₂ k := fun k => by
    simp only [slotW, m₄, o₄ sb (by decide), m₃, o₃ sb (by decide)]
  have kp₄ : s₄.gpr kp = s.gpr kp + BitVec.ofNat 32 128 := by
    rw [o₄ _ (by decide), kp₃, k₂, k₁]; rfl
  refine ⟨s₄, ?_, c₃.regs (fun r _ h => o₄ r h) m₄ rd₄ wr₄, hk.add (n := 2) kp₄, ⟨?_, ?_⟩, ?_,
    fun k h1 h2 => ?_⟩
  · rw [pairBody, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some,
      show ([addI kp 128, movS .eax grpSlot, .alu .cmp .eax (.reg kp)] : List Instr) =
        [addI kp 128] ++ [movS .eax grpSlot, .alu .cmp .eax (.reg kp)] from rfl,
      runBlock_app, e₃, Option.bind_some, e₄]
  · exact d₂.congr fun i _ => hs₄ _
  · exact d₂'.congr fun i _ => hs₄ _
  · rw [z₄, show s₃.gpr kp = s₄.gpr kp from (o₄ _ (by decide)).symm]
    have : slotW s₃ grpSlot = slotW s grpSlot := by
      rw [show slotW s₃ grpSlot = slotW s₂ grpSlot by simp only [slotW, m₃, o₃ sb (by decide)],
        a₂ _ (by rw [grpSlot_eq, tailSlot_eq]; decide) (by rw [grpSlot_eq, slots_eq]; decide),
        a₁ _ (by rw [grpSlot_eq, tailSlot_eq]; decide) (by rw [grpSlot_eq, slots_eq]; decide)]
    rw [this]
  · rw [hs₄, a₂ k h1 h2, a₁ k h1 h2]

/-- The FL layer: FLINV on `D2` with entry `m + 1`, FL on `D1` with entry `m`. -/
theorem fl_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa flLayer s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      Halves s' (fun b => (Spec.Camellia.fl (S b).1 (E m), Spec.Camellia.flinv (S b).2 (E (m + 1)))) ∧
      (∀ k, tailSlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  obtain ⟨h1, h2⟩ := hS
  have hok := hc.ok hp hk hm34
  have hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32 := by rw [hc.base]; exact hp.scr.fit
  have hK1 : W32.HalfRel (fun j => keyW s (16 + j)) fun _ => E (m + 1) := by
    simpa using hc.keyRel hp hk (e := 1) (by omega)
  obtain ⟨s₁, e₁, d₁, p₁⟩ := flinv_ok hok (d := d2Slot) (off := 16) (by decide) (by decide) h2 hK1
  have hK0 : W32.HalfRel (fun j => keyW s₁ (0 + j)) fun _ => E m := by
    have := hc.keyRel hp hk (e := 0) (by omega)
    refine (this.congr fun j hj => ?_).congr_right fun _ _ => by simp
    rw [p₁.keys _ (by omega)]
  have h1' : W32.HalfRel (half s₁ d1Slot) (fun b => (S b).1) :=
    h1.congr fun i hi => p₁.slots _ (by rw [d1Slot_eq, tailSlot_eq]; omega) (.inl (by rw [d1Slot_eq, d2Slot_eq]; omega))
  obtain ⟨s₂, e₂, d₂, p₂⟩ := fl_ok p₁.ok (d := d1Slot) (off := 0) (by decide) (by decide) h1' hK0
  have b₁ : s₁.gpr sb = s.gpr sb := p₁.gpr _ (by decide)
  obtain ⟨s₃, e₃, kp₃, -, o₃, m₃, rd₃, wr₃⟩ := addI_ok s₂ kp 128
  have kp₂ : s₂.gpr kp = s.gpr kp := (p₂.gpr _ (by decide)).trans (p₁.gpr _ (by decide))
  have hs₃ : ∀ k, slotW s₃ k = slotW s₂ k := fun k => by simp only [slotW, m₃, o₃ sb (by decide)]
  refine ⟨s₃, ?_, ?_, ?_, ⟨?_, ?_⟩, fun k k1 k2 => ?_⟩
  · rw [flLayer, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃]
  · have c₁ := hc.stepL p₁.rd p₁.wr (fun r h1 _ => p₁.gpr r fun h => h1 (by subst h; decide)) p₁.frame
    have c₂ := c₁.stepL p₂.rd p₂.wr (fun r h1 _ => p₂.gpr r fun h => h1 (by subst h; decide)) p₂.frame
    exact c₂.regs (fun r h _ => o₃ r h) m₃ rd₃ wr₃
  · exact hk.add (n := 2) (by rw [kp₃, kp₂]; rfl)
  · exact d₂.congr fun i _ => by simp only [half]; rw [hs₃]
  · refine d₁.congr fun i hi => ?_
    simp only [half]
    rw [hs₃, p₂.slots _ (by rw [d2Slot_eq, tailSlot_eq]; omega) (.inr (by rw [d1Slot_eq, d2Slot_eq]; omega))]
  · rw [hs₃, slot_above_frame (by rw [b₁]; exact hfit) (by rw [p₂.gpr _ (by decide)]) p₂.frame k1 k2,
      slot_above_frame hfit b₁ p₁.frame k1 k2]

/-! ## Groups of six rounds -/

/-- `mov eax, kp; add eax, 384; mov [edi + 4 grpSlot], eax`: the end of the group's pairs. -/
theorem setGrp_ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa [movR .eax kp, addI .eax 384, st grpSlot .eax] s = some s' ∧ Ctx s₀ s' ∧
      s'.gpr kp = s.gpr kp ∧ slotW s' grpSlot = s.gpr kp + BitVec.ofNat 32 384 ∧
      (∀ k < slots, k ≠ grpSlot → slotW s' k = slotW s k) := by
  have hs := hc.scr hp
  have hfit := hs.fit
  rw [slots_eq] at hfit
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁, -, -⟩ := movR_ok s .eax kp
  obtain ⟨s₂, e₂, r₂, -, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ .eax 384
  have b₂ : s₂.gpr sb = s.gpr sb := by rw [o₂ _ (by decide), o₁ _ (by decide)]
  have hin : InRegions s₂.wr (wordAddr (s₂.gpr sb) grpSlot) 4 := by
    rw [wr₂, wr₁, b₂]; exact hs.slot (by rw [grpSlot_eq, slots_eq]; decide)
  have hst : exec (st grpSlot .eax) s₂ =
      some { s₂ with mem := s₂.mem.writeW (wordAddr (s₂.gpr sb) grpSlot) (s₂.gpr .eax) } := by
    show s₂.store32 (wordAddr (s₂.gpr sb) grpSlot) (s₂.gpr .eax) = _
    simp only [State.store32, hin, ↓reduceIte]
  have hm : s₂.mem = s.mem := m₂.trans m₁
  refine ⟨{ s₂ with mem := s₂.mem.writeW (wordAddr (s₂.gpr sb) grpSlot) (s₂.gpr .eax) }, ?_, ?_, ?_, ?_,
    fun k hk hne => ?_⟩
  · rw [show ([movR .eax kp, addI .eax 384, st grpSlot .eax] : List Instr) =
      [movR .eax kp] ++ ([addI .eax 384] ++ [st grpSlot .eax]) from rfl, runBlock_app, e₁, Option.bind_some,
      runBlock_app, e₂, Option.bind_some, runBlock_cons, hst, runStep_some, runBlock_nil]
  · refine hc.step (rd₂.trans rd₁) (wr₂.trans wr₁) (fun r h1 h2 => ?_) ?_
    · show s₂.gpr r = s.gpr r
      have : r ≠ .eax := fun h => h1 (by subst h; decide)
      rw [o₂ r this, o₁ r this]
    · show Frame _ s.mem (s₂.mem.writeW (wordAddr (s₂.gpr sb) grpSlot) (s₂.gpr .eax))
      rw [hm, b₂, hc.base]
      exact (Frame.refl _ _).writeW (r := ⟨wordAddr (s₀.gpr sb) grpSlot, 4⟩) (by simp [ctxRegions]) _
        (Region.contains_self _ _)
  · show s₂.gpr kp = s.gpr kp
    rw [o₂ _ (by decide), o₁ _ (by decide)]
  · show (s₂.mem.writeW (wordAddr (s₂.gpr sb) grpSlot) (s₂.gpr .eax)).readW (wordAddr (s₂.gpr sb) grpSlot) 32 = _
    rw [Mem.readW_writeW_self32, r₂, r₁]; rfl
  · rw [slots_eq] at hk
    show (s₂.mem.writeW (wordAddr (s₂.gpr sb) grpSlot) (s₂.gpr .eax)).readW (wordAddr (s₂.gpr sb) k) 32 = _
    rw [Mem.readW_writeW_sep (slot_sep _ (by rw [b₂]; omega) (by rw [b₂, grpSlot_eq]; omega) hne) (by decide), b₂, hm]

/-- Whether `kp` is at the postwhitening's entry. -/
theorem atEnd_ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m ≤ 8 * g + 2) :
    ∃ s', runBlock isa (atEnd g) s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) m ∧
      s'.zf = some (decide (m = 8 * g)) ∧ (∀ k, slotW s' k = slotW s k) := by
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega
  obtain ⟨s', e', z', o', m', rd', wr'⟩ := endTest_ok s (BitVec.ofNat 32 (4 * keySlot + 512 * g))
  refine ⟨s', e', hc.regs (fun r _ h => o' r h) m' rd' wr', by rw [AtEntry, o' _ (by decide)]; exact hk, ?_,
    fun k => by simp only [slotW, m', o' sb (by decide)]⟩
  rw [z', show s.gpr kp = _ from hk, show s.gpr .edi = s₀.gpr sb from hc.base,
    VG.Offset.add_sub_cancel_left, ofNat32_sub_beq (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)]
  simp only [Option.some.injEq, decide_eq_decide]; omega

/-- A group of six rounds, then FL and FLINV unless it is the last. -/
theorem group_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {i : Nat} (hi : i < g) (hk : AtEntry s (s₀.gpr sb) (2 + 8 * i)) {S : Nat → BitVec 64 × BitVec 64}
    (hS : Halves s S) :
    WP isa (groupBody g) s fun s' => Ctx s₀ s' ∧ Halves s' (fun b => group g E (S b) i) ∧
      AtEntry s' (s₀.gpr sb) (if i + 1 < g then 2 + 8 * (i + 1) else 8 * g) ∧
      s'.zf = some (decide (i + 1 = g)) := by
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega
  let b := s₀.gpr sb
  -- The end of the pairs.
  obtain ⟨s₁, e₁, c₁, k₁, v₁, o₁⟩ := setGrp_ok hp.toKeyCtx hc
  have hk₁ : AtEntry s₁ b (2 + 8 * i) := by rw [AtEntry, k₁]; exact hk
  have hv₁ : slotW s₁ grpSlot = b + BitVec.ofNat 32 (4 * keySlot + 64 * (8 + 8 * i)) := by
    rw [v₁, show s.gpr kp = _ from hk, VG.Offset.add_add]; congr 2; omega
  have hS₁ : Halves s₁ S := hS.congr fun k h1 h2 =>
    o₁ k (by rw [slots_eq]; rw [tailSlot_eq] at h2; omega) (by rw [grpSlot_eq]; rw [tailSlot_eq] at h2; omega)
  unfold groupBody
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  -- The pairs.
  let Inv : Nat → State → Prop := fun n s' => ∃ p, n = 3 - p ∧ p < 3 ∧ Ctx s₀ s' ∧
    AtEntry s' b (2 + 8 * i + 2 * p) ∧ slotW s' grpSlot = slotW s₁ grpSlot ∧
    Halves s' (fun b => pairsN E i p (S b))
  let Mid : State → Prop := fun s' => Ctx s₀ s' ∧ AtEntry s' b (8 + 8 * i) ∧
    Halves s' (fun b => pairsN E i 3 (S b))
  refine WP.seq (WP.mono (Q := Mid) (WP.loop Inv (fun n s' hs' => ?_) 3 s₁
    ⟨0, rfl, by omega, c₁, by simpa using hk₁, rfl, by simpa [pairsN] using hS₁⟩) fun s₂ h₂ => ?_)
  · obtain ⟨p, rfl, hp3, hc', hk', hg', hS'⟩ := hs'
    obtain ⟨s'', e'', c'', k'', S'', z'', a''⟩ := pair_step hp.toKeyCtx hc' hk' (by omega) (by omega) hS'
    refine WP.of_runBlock ⟨s'', e'', ?_⟩
    have hz : s''.zf = some (decide (p + 1 = 3)) := by
      rw [z'', show s''.gpr kp = _ from k'', hg', hv₁, entry_beq b (by rw [keySlot_eq]; omega)
        (by rw [keySlot_eq]; omega)]
      simp only [Option.some.injEq, decide_eq_decide]; omega
    have hS'' : Halves s'' (fun b => pairsN E i (p + 1) (S b)) := by
      simpa only [pairsN_succ, show 2 + 8 * i + 2 * p + 1 = 3 + 8 * i + 2 * p by omega] using S''
    by_cases hp2 : p + 1 = 3
    · refine .inl ⟨(eval_ne s'').trans (by rw [hz]; simp [hp2]), c'', ?_, by rw [← hp2]; exact hS''⟩
      rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 8 + 8 * i by omega]
    · refine .inr ⟨(eval_ne s'').trans (by rw [hz]; simp [hp2]), 3 - (p + 1), by omega, p + 1, rfl, by omega, c'',
        by rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 2 + 8 * i + 2 * (p + 1) by omega],
        by rw [a'' _ (by rw [grpSlot_eq, tailSlot_eq]; decide) (by rw [grpSlot_eq, slots_eq]; decide), hg'], hS''⟩
  · obtain ⟨hc₂, hk₂, hS₂⟩ := h₂
    obtain ⟨s₃, e₃, hc₃, hk₃, hz₃, sl₃⟩ := atEnd_ok hp hc₂ hk₂ (by omega)
    have hS₃ : Halves s₃ (fun b => pairsN E i 3 (S b)) := hS₂.congr fun k _ _ => sl₃ k
    refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
    refine WP.seq (WP.ite (!decide (8 + 8 * i = 8 * g)) ((eval_ne s₃).trans (by rw [hz₃]; rfl)) (fun ht => ?_)
      (fun hf => ?_))
    · have hlt : i + 1 < g := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at ht; omega
      obtain ⟨s₄, e₄, c₄, k₄, S₄, -⟩ := fl_step hp.toKeyCtx hc₃ hk₃ (by omega) (by omega) hS₃
      refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
      have hk₄ : AtEntry s₄ b (2 + 8 * (i + 1)) := by
        rw [AtEntry, show s₄.gpr kp = _ from k₄, show 8 + 8 * i + 2 = 2 + 8 * (i + 1) by omega]
      obtain ⟨s₅, e₅, c₅, k₅, z₅, sl₅⟩ := atEnd_ok hp c₄ hk₄ (by omega)
      refine WP.of_runBlock ⟨s₅, e₅, c₅, ?_, ?_, ?_⟩
      · have hG : (fun b => group g E (S b) i) = fun b =>
            (Spec.Camellia.fl (pairsN E i 3 (S b)).1 (E (8 + 8 * i)),
              Spec.Camellia.flinv (pairsN E i 3 (S b)).2 (E (8 + 8 * i + 1))) :=
          funext fun b => by
            rw [group_eq, show 8 + 8 * i + 1 = 9 + 8 * i by omega]; simp only [hlt, ↓reduceIte]
        rw [hG]
        exact S₄.congr fun k _ _ => sl₅ k
      · simp only [hlt, ↓reduceIte]; exact k₅
      · rw [z₅]; simp only [Option.some.injEq, decide_eq_decide]; omega
    · have heq : i + 1 = g := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hf; omega
      refine WP.of_runBlock ⟨s₃, rfl, ?_⟩
      obtain ⟨s₅, e₅, c₅, k₅, z₅, sl₅⟩ := atEnd_ok hp hc₃ hk₃ (by omega)
      refine WP.of_runBlock ⟨s₅, e₅, c₅, ?_, ?_, ?_⟩
      · have hG : (fun b => group g E (S b) i) = fun b => pairsN E i 3 (S b) :=
          funext fun b => by rw [group_eq]; simp only [show ¬ i + 1 < g by omega, ↓reduceIte]
        rw [hG]
        exact hS₃.congr fun k _ _ => sl₅ k
      · simp only [show ¬ i + 1 < g by omega, ↓reduceIte]
        rw [show 8 * g = 8 + 8 * i by omega]; exact k₅
      · rw [z₅]; simp only [Option.some.injEq, decide_eq_decide]; omega

end VG.Proof.Camellia.X86
