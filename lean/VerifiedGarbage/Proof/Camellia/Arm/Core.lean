module

import VerifiedGarbage.Proof.Camellia.Arm.Fl
public import VerifiedGarbage.Proof.Camellia.Words
public import VerifiedGarbage.Proof.Camellia.Arm.Round
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Eight blocks of bitsliced Camellia on ARMv7: the rounds

With the table of bitsliced subkeys `E 0 … E (8 g + 1)` in the scratch
buffer (`CorePre`), the groups of rounds of `crypt8` take the halves in
their slots through `groups g E`. They write only the rounds' working space
below the table and the slot of the group's end (`Ctx`). The rounds are
`round_ok`, FL and FLINV `fl_ok` and `flinv_ok`; the pairs of rounds and the
groups of six are loops around them, whose invariants are the
specification's `pair` and `group` (`Proof/Camellia/Words.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Camellia.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp ldS stS)
open VG.Proof.Camellia (pair group groups cryptWords pairsN pairsN_succ group_eq)
open VG.Proof.Sm4.Arm (linPostG)

theorem slots_eq : slots = 680 := rfl
theorem tailSlot_eq : tailSlot = 632 := rfl
theorem keySlot_eq : keySlot = 72 := rfl
theorem grpSlot_eq : grpSlot = 616 := rfl
theorem endSlot_eq : endSlot = 617 := rfl
theorem d1Slot_eq : d1Slot = 40 := rfl
theorem d2Slot_eq : d2Slot = 56 := rfl

/-- Word `j` of entry `i` of the table, in the scratch buffer at `b`. -/
def entryW (m : Mem) (b : BitVec 32) (i j : Nat) : BitVec 32 := m.readW (wordAddr b (keySlot + 16 * i + j)) 32

/-- The scratch buffer at `b` is writable in `s`, and does not wrap around. -/
structure Scr (s : State) (b : BitVec 32) : Prop where
  wr : (⟨State.addr b, 4 * slots⟩ : Region) ∈ s.wr
  fit : b.toNat + 4 * slots ≤ 2 ^ 32

/-- What the rounds need: the scratch buffer, writable, and a table of `nk`
subkeys. -/
structure KeyCtx (s₀ : State) (nk : Nat) (E : Nat → BitVec 64) : Prop where
  scr : Scr s₀ (s₀.gpr sb)
  nk34 : nk ≤ 34
  keys : ∀ i < nk, W32.HalfRel (entryW s₀.mem (s₀.gpr sb) i) fun _ => E i

/-- What the groups of rounds need: the table of `8 g + 2` subkeys, and the
address of its postwhitening entry in its slot. -/
structure CorePre (s₀ : State) (g : Nat) (E : Nat → BitVec 64) : Prop extends KeyCtx s₀ (8 * g + 2) E where
  hg : g = 3 ∨ g = 4
  bound : slotW s₀ endSlot = s₀.gpr sb + BitVec.ofNat 32 (4 * keySlot + 512 * g)

/-- What the rounds may write in the scratch buffer at `b`: their working
space, the slot of the group's end, and the tail buffer. -/
def ctxRegions (b : BitVec 32) : List Region :=
  [⟨State.addr b, 4 * keySlot⟩, ⟨State.addr (b + BitVec.ofNat 32 (4 * grpSlot)), 4⟩,
   ⟨State.addr (b + BitVec.ofNat 32 (4 * tailSlot)), 128⟩]

/-- What stays the same: the regions, `sb` and the registers outside the
layers', and the memory outside `ctxRegions`. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ layerWrites → r ≠ kp → s.gpr r = s₀.gpr r
  frame : Frame (ctxRegions (s₀.gpr sb)) s₀.mem s.mem

theorem Ctx.refl (s₀ : State) : Ctx s₀ s₀ := ⟨rfl, rfl, fun _ _ _ => rfl, Frame.refl _ _⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide)

/-- A step that writes only the layers' registers, `kp`, and the regions. -/
theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r)
    (hf : Frame (ctxRegions (s₀.gpr sb)) s.mem s'.mem) : Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 => (hk r h1 h2).trans (hc.keep r h1 h2), hc.frame.trans hf⟩

/-- A step that writes only the rounds' working space. -/
theorem Ctx.stepL {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r)
    (hf : Frame [slotRegion layerCfg s] s.mem s'.mem) : Ctx s₀ s' :=
  hc.step hrd hwr hk (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    simp [slotRegion, layerCfg, ctxRegions, hc.base])

/-! ## Addresses -/

/-- `kp` at entry `m` of the table. -/
def AtEntry (s : State) (b : BitVec 32) (m : Nat) : Prop := s.gpr kp = b + BitVec.ofNat 32 (4 * keySlot + 64 * m)

theorem wordAddr_entry {s : State} {b : BitVec 32} {m : Nat} (hk : AtEntry s b m) (j : Nat) :
    wordAddr (s.gpr kp) j = wordAddr b (keySlot + 16 * m + j) := by
  rw [wordAddr, wordAddr, hk, add_ofNat_ofNat,
    show 4 * keySlot + 64 * m + 4 * j = 4 * (keySlot + 16 * m + j) by omega]

theorem keyW_entry {s : State} {b : BitVec 32} {m : Nat} (hk : AtEntry s b m) (e j : Nat) :
    keyW s (16 * e + j) = entryW s.mem b (m + e) j := by
  simp only [keyW, entryW, wordAddr_entry hk,
    show keySlot + 16 * m + (16 * e + j) = keySlot + 16 * (m + e) + j by omega]

theorem Scr.slot_in {s : State} {b : BitVec 32} (h : Scr s b) {k : Nat} (hk : k < slots) :
    InRegions s.wr (wordAddr b k) 4 :=
  in_off h.wr h.fit (by omega) (by omega)

theorem ok_layer {s : State} {b : BitVec 32} {m : Nat} (hs : Scr s b) (hb : s.gpr sb = b)
    (hk : AtEntry s b m) (hm : m + 2 ≤ 34) : Ok layerCfg s where
  slotIn k hk' := by
    simp only [layerCfg, keySlot_eq] at hk'
    simp only [layerCfg, hb]; exact hs.slot_in (by rw [slots_eq]; omega)
  extIn j hj := by
    simp only [layerCfg] at hj
    simp only [layerCfg, wordAddr_entry hk]
    obtain ⟨r, hr, hc⟩ := hs.slot_in (k := keySlot + 16 * m + j) (by rw [slots_eq, keySlot_eq]; omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  slots := by have := hs.fit; simp only [layerCfg, hb]; rw [slots_eq] at this; rw [keySlot_eq]; omega
  sep k hk' j hj := by
    have := hs.fit
    simp only [layerCfg, keySlot_eq] at hk' hj
    simp only [layerCfg, hb, wordAddr_entry hk]
    rw [slots_eq] at this
    exact slot_sep _ (by omega) (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)

/-- A word of slot `k` outside a region at slots `a … a + n` of the scratch buffer. -/
theorem slot_disjoint {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k a n : Nat}
    (hk : k < slots) (ha : a + n ≤ slots) (hn : 0 < n) (h : k + 1 ≤ a ∨ a + n ≤ k) :
    (⟨wordAddr b k, 4⟩ : Region).Disjoint ⟨State.addr (b + BitVec.ofNat 32 (4 * a)), 4 * n⟩ := by
  rw [slots_eq] at hfit hk ha
  rw [wordAddr, VG.Arm.addr_add (by omega), VG.Arm.addr_add (by omega)]
  exact VG.Offset.disjoint _ (by omega) (by omega) (by omega)

theorem slot_disjoint_base {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k n : Nat}
    (hk : k < slots) (hn : n ≤ k) :
    (⟨wordAddr b k, 4⟩ : Region).Disjoint ⟨State.addr b, 4 * n⟩ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · intro x _ h; simp [Region.Contains] at h
  have := slot_disjoint hfit (a := 0) (n := n) hk (by rw [slots_eq] at hk ⊢; omega) hn0 (.inr (by omega))
  simpa using this

/-- Slots outside `ctxRegions` are kept. -/
theorem Ctx.slot {s₀ s : State} (hc : Ctx s₀ s) (hfit : (s₀.gpr sb).toNat + 4 * slots ≤ 2 ^ 32) {k : Nat}
    (hk : k < slots) (h1 : keySlot ≤ k) (h2 : k ≠ grpSlot) (h3 : k < tailSlot ∨ tailSlot + 32 ≤ k) :
    slotW s k = slotW s₀ k := by
  simp only [slotW, hc.base]
  refine hc.frame.readW (r := ⟨wordAddr (s₀.gpr sb) k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact slot_disjoint_base hfit hk h1
  · have := slot_disjoint hfit (a := grpSlot) (n := 1) hk (by rw [slots_eq, grpSlot_eq]; omega)
      (by decide) (by omega)
    simpa using this
  · have := slot_disjoint hfit (a := tailSlot) (n := 32) hk (by rw [slots_eq, tailSlot_eq]; omega)
      (by decide) (by omega)
    simpa using this

theorem Ctx.entry {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {i j : Nat} (hi : i < 34) (hj : j < 16) :
    entryW s.mem (s₀.gpr sb) i j = entryW s₀.mem (s₀.gpr sb) i j := by
  have := hc.slot hp.scr.fit (k := keySlot + 16 * i + j) (by rw [slots_eq, keySlot_eq]; omega)
    (by omega) (by rw [grpSlot_eq, keySlot_eq]; omega) (.inl (by rw [tailSlot_eq, keySlot_eq]; omega))
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
  ok_layer ⟨by rw [hc.wr]; exact hp.scr.wr, hp.scr.fit⟩ hc.base hk hm

/-! ## Rounds -/

/-- The halves of the eight blocks, `(D1, D2)` of block `b` in `S b`, in their slots. -/
def Halves (s : State) (S : Nat → BitVec 64 × BitVec 64) : Prop :=
  W32.HalfRel (half s d1Slot) (fun b => (S b).1) ∧ W32.HalfRel (half s d2Slot) (fun b => (S b).2)

theorem Halves.congr {s s' : State} {S : Nat → BitVec 64 × BitVec 64} (h : Halves s S)
    (hs : ∀ k, d1Slot ≤ k → k < keySlot → slotW s' k = slotW s k) : Halves s' S :=
  ⟨h.1.congr fun i hi => hs _ (by omega) (by rw [d1Slot_eq, keySlot_eq] at *; omega),
   h.2.congr fun i hi => hs _ (by rw [d1Slot_eq, d2Slot_eq]; omega) (by rw [d2Slot_eq, keySlot_eq]; omega)⟩

theorem round_all (off src dst : Nat) (h : RoundCase off src dst) :
    (layerKeep.all fun r => (preL off src ++ midLR off src ++ postP dst).all fun i => !clobbers i r) = true := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide +kernel

/-- `add kp, kp, #n`, keeping all else. -/
theorem addKp_ok (s : State) (n : Nat) (he : encodable (BitVec.ofNat 32 n) = true) :
    runBlock isa [.dp .add kp kp (.imm (BitVec.ofNat 32 n))] s =
      some (s.setReg kp (s.gpr kp + BitVec.ofNat 32 n)) := by
  simp only [runBlock_cons, exec, Op2.eval, he, ↓reduceIte, Option.map_some, runStep_some, runBlock_nil]

/-- A round, under `Ctx`, with the subkey at entry `m + off / 16`. -/
theorem round_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {off src dst m : Nat}
    (hA : check (lanes 32 11) layerCfg (linExt 32) (preL off src) preEnv
      (linPostG 11 (qOuts (preG off src)) [] halvesSlots preEnv) = true)
    (hC : check (lanes 32 12) layerCfg (linExt 40) (midLR off src) midEnv
      (linPostG 12 (qOuts (midG off src)) ylOuts halvesSlots midEnv) = true)
    (hE : check (lanes 32 11) linCfg (linExt 48) (postP dst) postEnv
      (linPostG 11 [] (postOuts dst) (otherSlots dst) postEnv) = true)
    (hcase : RoundCase off src dst)
    (hk : AtEntry s (s₀.gpr sb) m) (hme : m + off / 16 < nk) (hm34 : m + 2 ≤ 34)
    {X Y : Nat → BitVec 64} (hQ : W32.HalfRel (half s src) X) (hR : W32.HalfRel (half s dst) Y) :
    ∃ s', runBlock isa (round off src dst) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      W32.HalfRel (half s' dst) (fun b => Y b ^^^ Spec.Camellia.f (X b) (E (m + off / 16))) ∧
      (∀ i < 16, slotW s' (src + i) = slotW s (src + i)) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  have hK : W32.HalfRel (fun j => keyW s (off + j)) fun _ => E (m + off / 16) := by
    have := hc.keyRel hp hk (e := off / 16) hme
    rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact this
  have hok := hc.ok hp hk hm34
  obtain ⟨s', h', hD, hsrc, rd', wr', sp', o', f'⟩ :=
    round_ok hA hC hE (round_all off src dst hcase) hcase hok hQ hK hR
  have hfit := hp.scr.fit
  rw [slots_eq] at hfit
  refine ⟨s', h', hc.stepL rd' wr' (fun r h1 _ => o' r h1) f', o' _ (by decide), hD, hsrc, fun k h1 h2 => ?_⟩
  simp only [slotW, o' sb (by decide)]
  refine f'.readW (r := ⟨wordAddr (s.gpr sb) k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  simp only [slotRegion, layerCfg]
  rw [hc.base]
  exact slot_disjoint_base (by rw [slots_eq]; omega) h2 h1

theorem entry_beq (b : BitVec 32) {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (b + BitVec.ofNat 32 x - (b + BitVec.ofNat 32 y) == 0) = decide (x = y) := by
  rw [VG.Offset.add_sub_add_left, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

/-- `ldr t0, [sb, #4 grpSlot]; cmp kp, t0`. -/
theorem cmpSlot_ok {s : State} (hs : Scr s (s.gpr sb)) {k : Nat} (hk : k < slots) (hk4 : 4 * k < 4096) :
    runBlock isa [ldS t0 k, .cmp kp (.reg t0)] s =
      some (subFlags (s.setReg t0 (slotW s k)) (s.gpr kp) (slotW s k)) := by
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr sb + BitVec.ofNat 32 (4 * k))) 4 := by
    obtain ⟨r, hr, hc⟩ := hs.slot_in hk; exact ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [ldS, runBlock_cons, exec_ldr hk4 hin, runStep_some]
  rfl

theorem subFlags_gpr (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
theorem subFlags_mem (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
theorem subFlags_rd (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
theorem subFlags_wr (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
theorem subFlags_z (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0) := rfl

theorem encodable_128 : encodable (BitVec.ofNat 32 128) = true := by decide

/-- `kp` stepped by `n`, from entry `m`. -/
theorem AtEntry.add {s s' : State} {b : BitVec 32} {m n : Nat} (hk : AtEntry s b m)
    (h : s'.gpr kp = s.gpr kp + BitVec.ofNat 32 (64 * n)) : AtEntry s' b (m + n) := by
  rw [AtEntry, h, hk, add_ofNat_ofNat]; congr 2; omega

/-- The two rounds of a pair, `kp += 128` and the comparison of `kp` with the
group's end. -/
theorem pair_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa pairBody s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      Halves s' (fun b => pair (E m) (E (m + 1)) (S b)) ∧
      s'.z = (s'.gpr kp - slotW s grpSlot == 0) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
  obtain ⟨h1, h2⟩ := hS
  obtain ⟨s₁, e₁, c₁, k₁, d₁, o₁, a₁⟩ := round_step hp hc (off := 0) (src := d1Slot) (dst := d2Slot)
    preL0_check mid0_check post2_check (.inl ⟨rfl, rfl, rfl⟩) hk (by omega) hm34 h1 h2
  have hk₁ : AtEntry s₁ (s₀.gpr sb) m := by rw [AtEntry, k₁]; exact hk
  have h1' : W32.HalfRel (half s₁ d1Slot) (fun b => (S b).1) := h1.congr fun i hi => o₁ i hi
  obtain ⟨s₂, e₂, c₂, k₂, d₂, o₂, a₂⟩ := round_step hp c₁ (off := 16) (src := d2Slot) (dst := d1Slot)
    preL16_check mid16_check post1_check (.inr ⟨rfl, rfl, rfl⟩) hk₁ (by omega) hm34 d₁ h1'
  have d₂' : W32.HalfRel (half s₂ d2Slot) (fun b => (S b).2 ^^^ Spec.Camellia.f (S b).1 (E (m + 0 / 16))) :=
    d₁.congr fun i hi => o₂ i hi
  let s₃ := s₂.setReg kp (s₂.gpr kp + BitVec.ofNat 32 128)
  have ok₃ : Scr s₃ (s₃.gpr sb) := by
    have : s₃.gpr sb = s₀.gpr sb := (RegUpd.gpr_setReg_of_ne _ _ (by decide)).trans c₂.base
    rw [this]; exact ⟨by rw [show s₃.wr = s₂.wr from rfl, c₂.wr]; exact hp.scr.wr, hp.scr.fit⟩
  have hfit := hp.scr.fit
  rw [slots_eq] at hfit
  have hs₃ : ∀ k, slotW s₃ k = slotW s₂ k := fun k => slotW_setReg _ _ (by decide) k
  have g₄ : ∀ r, r ≠ t0 → r ≠ kp →
      (subFlags (s₃.setReg t0 (slotW s₃ grpSlot)) (s₃.gpr kp) (slotW s₃ grpSlot)).gpr r = s₂.gpr r :=
    fun r h1 h2 => by
      rw [subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_setReg_of_ne _ _ h2]
  have hs₄ : ∀ k, slotW (subFlags (s₃.setReg t0 (slotW s₃ grpSlot)) (s₃.gpr kp) (slotW s₃ grpSlot)) k =
      slotW s₂ k := fun k => by
    simp only [slotW, subFlags_mem, RegUpd.mem_setReg, g₄ sb (by decide) (by decide)]
    rfl
  have kp₄ : (subFlags (s₃.setReg t0 (slotW s₃ grpSlot)) (s₃.gpr kp) (slotW s₃ grpSlot)).gpr kp =
      s.gpr kp + BitVec.ofNat 32 128 := by
    rw [subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self, k₂, k₁]
  refine ⟨subFlags (s₃.setReg t0 (slotW s₃ grpSlot)) (s₃.gpr kp) (slotW s₃ grpSlot), ?_, ?_, ?_, ⟨?_, ?_⟩, ?_,
    fun k h1 h2 => ?_⟩
  · rw [pairBody, runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some,
      show ([.dp .add kp kp (.imm 128), ldS t0 grpSlot, .cmp kp (.reg t0)] : List Instr) =
        [.dp .add kp kp (.imm (BitVec.ofNat 32 128))] ++ [ldS t0 grpSlot, .cmp kp (.reg t0)] from rfl,
      runBlock_app, addKp_ok _ _ encodable_128, Option.bind_some,
      cmpSlot_ok ok₃ (by rw [grpSlot_eq, slots_eq]; decide) (by rw [grpSlot_eq]; decide)]
  · refine c₂.step rfl rfl (fun r h1 h2 => g₄ r (fun h => h1 (h ▸ by decide)) h2) (by exact Frame.refl _ _)
  · exact hk.add (n := 2) kp₄
  · exact d₂.congr fun i _ => hs₄ _
  · exact d₂'.congr fun i _ => hs₄ _
  · have : s₃.gpr kp = s.gpr kp + BitVec.ofNat 32 128 := by
      rw [RegUpd.gpr_setReg_self, k₂, k₁]
    rw [subFlags_z, kp₄, this, hs₃, a₂ _ (by rw [grpSlot_eq, keySlot_eq]; decide)
      (by rw [grpSlot_eq, slots_eq]; decide), a₁ _ (by rw [grpSlot_eq, keySlot_eq]; decide)
      (by rw [grpSlot_eq, slots_eq]; decide)]
  · rw [hs₄, a₂ k h1 h2, a₁ k h1 h2]

/-- A frame of the rounds' working space keeps the slots from the table on. -/
theorem slot_above_frame {s s' : State} (hfit : (s.gpr sb).toNat + 4 * slots ≤ 2 ^ 32)
    (hb : s'.gpr sb = s.gpr sb) (hf : Frame [slotRegion layerCfg s] s.mem s'.mem) {k : Nat}
    (h1 : keySlot ≤ k) (h2 : k < slots) : slotW s' k = slotW s k := by
  simp only [slotW, hb]
  refine hf.readW (r := ⟨wordAddr (s.gpr sb) k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact slot_disjoint_base hfit h2 h1

/-- The FL layer: FLINV on `D2` with entry `m + 1`, FL on `D1` with entry `m`. -/
theorem fl_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa flLayer s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      Halves s' (fun b => (Spec.Camellia.fl (S b).1 (E m), Spec.Camellia.flinv (S b).2 (E (m + 1)))) ∧
      (∀ k, keySlot ≤ k → k < slots → slotW s' k = slotW s k) := by
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
    h1.congr fun i hi => p₁.slots _ (by rw [d1Slot_eq, keySlot_eq]; omega) (.inl (by rw [d1Slot_eq, d2Slot_eq]; omega))
  obtain ⟨s₂, e₂, d₂, p₂⟩ := fl_ok p₁.ok (d := d1Slot) (off := 0) (by decide) (by decide) h1' hK0
  have b₁ : s₁.gpr sb = s.gpr sb := p₁.gpr _ (by decide)
  have b₂ : s₂.gpr sb = s.gpr sb := (p₂.gpr _ (by decide)).trans b₁
  have kp₂ : s₂.gpr kp = s.gpr kp := (p₂.gpr _ (by decide)).trans (p₁.gpr _ (by decide))
  have hs₃ : ∀ k, slotW (s₂.setReg kp (s₂.gpr kp + BitVec.ofNat 32 128)) k = slotW s₂ k :=
    fun k => slotW_setReg _ _ (by decide) k
  refine ⟨s₂.setReg kp (s₂.gpr kp + BitVec.ofNat 32 128), ?_, ?_, ?_, ⟨?_, ?_⟩, fun k k1 k2 => ?_⟩
  · rw [show flLayer = flinvCode d2Slot 16 ++ flCode d1Slot 0 ++
        [.dp .add kp kp (.imm (BitVec.ofNat 32 128))] from rfl,
      runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, addKp_ok _ _ encodable_128]
  · have c₁ := hc.stepL p₁.rd p₁.wr (fun r h1 _ => p₁.gpr r h1) p₁.frame
    have e : slotRegion layerCfg s₁ = slotRegion layerCfg s := by simp only [slotRegion, layerCfg, b₁]
    have c₂ := c₁.stepL p₂.rd p₂.wr (fun r h1 _ => p₂.gpr r h1) p₂.frame
    exact c₂.step rfl rfl (fun r _ h2 => RegUpd.gpr_setReg_of_ne _ _ h2) (Frame.refl _ _)
  · exact hk.add (n := 2) (by rw [RegUpd.gpr_setReg_self, kp₂])
  · exact d₂.congr fun i _ => by simp only [half]; rw [hs₃]
  · refine d₁.congr fun i hi => ?_
    simp only [half]
    rw [hs₃, p₂.slots _ (by rw [d2Slot_eq, keySlot_eq]; omega) (.inr (by rw [d1Slot_eq, d2Slot_eq]; omega))]
  · rw [hs₃, slot_above_frame (by rw [b₁]; exact hfit) (by rw [p₂.gpr _ (by decide)]) p₂.frame k1 k2,
      slot_above_frame hfit b₁ p₁.frame k1 k2]

/-! ## Groups of six rounds -/

theorem Ctx.scr {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    Scr s (s.gpr sb) := ⟨by rw [hc.wr, hc.base]; exact hp.scr.wr, by rw [hc.base]; exact hp.scr.fit⟩

theorem encodable_384 : encodable (BitVec.ofNat 32 384) = true := by decide

/-- `add t0, kp, #384; str t0, [sb, #4 grpSlot]`: the end of the group's pairs. -/
theorem setGrp_ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa [.dp .add t0 kp (.imm 384), stS grpSlot t0] s = some s' ∧ Ctx s₀ s' ∧
      s'.gpr kp = s.gpr kp ∧ slotW s' grpSlot = s.gpr kp + BitVec.ofNat 32 384 ∧
      (∀ k < slots, k ≠ grpSlot → slotW s' k = slotW s k) := by
  have hs := hc.scr hp
  have hfit := hs.fit
  rw [slots_eq] at hfit
  let s₁ := s.setReg t0 (s.gpr kp + BitVec.ofNat 32 384)
  have b₁ : s₁.gpr sb = s.gpr sb := RegUpd.gpr_setReg_of_ne _ _ (by decide)
  have hst : exec (stS grpSlot t0) s₁ =
      some { s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) grpSlot) (s₁.gpr t0) } :=
    exec_str (by rw [grpSlot_eq]; decide) (by rw [b₁]; exact hs.slot_in (by rw [grpSlot_eq, slots_eq]; decide))
  refine ⟨{ s₁ with mem := s₁.mem.writeW (wordAddr (s₁.gpr sb) grpSlot) (s₁.gpr t0) }, ?_, ?_, ?_, ?_, fun k hk hne => ?_⟩
  · have ha : exec (.dp .add t0 kp (.imm (BitVec.ofNat 32 384))) s = some s₁ := by
      simp only [exec, Op2.eval, encodable_384, ↓reduceIte, Option.map_some]; rfl
    rw [show ([.dp .add t0 kp (.imm 384), stS grpSlot t0] : List Instr) =
      [.dp .add t0 kp (.imm (BitVec.ofNat 32 384)), stS grpSlot t0] from rfl, runBlock_cons, ha, runStep_some,
      runBlock_cons, hst, runStep_some, runBlock_nil]
  · refine hc.step rfl rfl (fun r h1 h2 => RegUpd.gpr_setReg_of_ne _ _ (fun h => h1 (by rw [h]; decide))) ?_
    refine (Frame.refl _ _).writeW (r := ⟨State.addr (s₀.gpr sb + BitVec.ofNat 32 (4 * grpSlot)), 4⟩)
      (by simp [ctxRegions]) _ ?_
    rw [b₁, hc.base]; exact Region.contains_self _ _
  · exact RegUpd.gpr_setReg_of_ne (r := t0) (r' := kp) s (s.gpr kp + BitVec.ofNat 32 384) (by decide)
  · show (s₁.mem.writeW (wordAddr (s₁.gpr sb) grpSlot) (s₁.gpr t0)).readW (wordAddr (s₁.gpr sb) grpSlot) 32 = _
    rw [Mem.readW_writeW_self32]; exact RegUpd.gpr_setReg_self _ _ _
  · rw [slots_eq] at hk
    show (s₁.mem.writeW (wordAddr (s₁.gpr sb) grpSlot) (s₁.gpr t0)).readW (wordAddr (s₁.gpr sb) k) 32 = _
    rw [Mem.readW_writeW_sep (slot_sep _ (by rw [b₁]; omega) (by rw [b₁, grpSlot_eq]; omega) hne) (by decide), b₁]
    rfl

/-- `ldr t0, [sb, #4 endSlot]; cmp kp, t0`: whether `kp` is at the postwhitening's entry. -/
theorem atEnd_ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m ≤ 8 * g + 2) :
    ∃ s', runBlock isa atEnd s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) m ∧
      s'.z = decide (m = 8 * g) ∧ (∀ k, slotW s' k = slotW s k) := by
  have hs := hc.scr hp.toKeyCtx
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega
  refine ⟨_, cmpSlot_ok hs (by rw [endSlot_eq, slots_eq]; decide) (by rw [endSlot_eq]; decide),
    hc.step rfl rfl (fun r h1 h2 => by rw [subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ (fun h => h1 (by rw [h]; decide))])
      (Frame.refl _ _), ?_, ?_, fun k => ?_⟩
  · rw [AtEntry, subFlags_gpr, RegUpd.gpr_setReg_of_ne _ _ (by decide)]; exact hk
  · rw [subFlags_z, hc.slot hp.scr.fit (by rw [endSlot_eq, slots_eq]; decide) (by rw [endSlot_eq, keySlot_eq]; decide)
      (by rw [endSlot_eq, grpSlot_eq]; decide) (.inl (by rw [endSlot_eq, tailSlot_eq]; decide)), hp.bound, hk,
      show 512 * g = 64 * (8 * g) by omega, entry_beq _ (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)]
    simp only [decide_eq_decide]; omega
  · simp only [slotW, subFlags_mem, subFlags_gpr, RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ (show sb ≠ t0 by decide)]

theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl

theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

/-- A group of six rounds, then FL and FLINV unless it is the last. -/
theorem group_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {i : Nat} (hi : i < g) (hk : AtEntry s (s₀.gpr sb) (2 + 8 * i)) {S : Nat → BitVec 64 × BitVec 64}
    (hS : Halves s S) :
    WP isa groupBody s fun s' => Ctx s₀ s' ∧ Halves s' (fun b => group g E (S b) i) ∧
      AtEntry s' (s₀.gpr sb) (if i + 1 < g then 2 + 8 * (i + 1) else 8 * g) ∧
      s'.z = decide (i + 1 = g) := by
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega
  let b := s₀.gpr sb
  -- The end of the pairs.
  obtain ⟨s₁, e₁, c₁, k₁, v₁, o₁⟩ := setGrp_ok hp.toKeyCtx hc
  have hk₁ : AtEntry s₁ b (2 + 8 * i) := by rw [AtEntry, k₁]; exact hk
  have hv₁ : slotW s₁ grpSlot = b + BitVec.ofNat 32 (4 * keySlot + 64 * (8 + 8 * i)) := by
    rw [v₁, hk, add_ofNat_ofNat]; congr 2; omega
  have hS₁ : Halves s₁ S := hS.congr fun k h1 h2 =>
    o₁ k (by rw [slots_eq]; rw [keySlot_eq] at h2; omega) (by rw [grpSlot_eq]; rw [keySlot_eq] at h2; omega)
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
    have hz : s''.z = decide (p + 1 = 3) := by
      rw [z'', show s''.gpr kp = _ from k'', hg', hv₁, entry_beq b (by rw [keySlot_eq]; omega)
        (by rw [keySlot_eq]; omega)]
      simp only [decide_eq_decide]; omega
    have hS'' : Halves s'' (fun b => pairsN E i (p + 1) (S b)) := by
      simpa only [pairsN_succ, show 2 + 8 * i + 2 * p + 1 = 3 + 8 * i + 2 * p by omega] using S''
    by_cases hp2 : p + 1 = 3
    · refine .inl ⟨(eval_ne s'').trans (by rw [hz]; simp [hp2]), c'', ?_, by rw [← hp2]; exact hS''⟩
      rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 8 + 8 * i by omega]
    · refine .inr ⟨(eval_ne s'').trans (by rw [hz]; simp [hp2]), 3 - (p + 1), by omega, p + 1, rfl, by omega, c'',
        by rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 2 + 8 * i + 2 * (p + 1) by omega],
        by rw [a'' _ (by rw [grpSlot_eq, keySlot_eq]; decide) (by rw [grpSlot_eq, slots_eq]; decide), hg'], hS''⟩
  · obtain ⟨hc₂, hk₂, hS₂⟩ := h₂
    obtain ⟨s₃, e₃, hc₃, hk₃, hz₃, sl₃⟩ := atEnd_ok hp hc₂ hk₂ (by omega)
    have hS₃ : Halves s₃ (fun b => pairsN E i 3 (S b)) := hS₂.congr fun k _ _ => sl₃ k
    refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
    refine WP.seq (WP.ite (!decide (8 + 8 * i = 8 * g)) ((eval_ne s₃).trans (by rw [hz₃])) (fun ht => ?_)
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
      · rw [z₅]; simp only [decide_eq_decide]; omega
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
      · rw [z₅]; simp only [decide_eq_decide]; omega

theorem WP.sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h; exact ⟨t, s', he, hq, Exec.sp he⟩

theorem addr_toNat (b : BitVec 32) : (State.addr b).toNat = b.toNat := by
  have := b.isLt; simp [State.addr]; omega
/-- The rounds' regions are in the scratch buffer. -/
theorem ctx_sub_scr {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) :
    ∀ r ∈ ctxRegions b, Region.Sub r ⟨State.addr b, 4 * slots⟩ := by
  have hb := addr_toNat b
  rw [slots_eq] at hfit
  intro r hr
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Region.sub_prefix (by rw [slots_eq, keySlot_eq] <;> omega)
  · rw [VG.Arm.addr_add (by rw [grpSlot_eq] <;> omega)]
    exact VG.Offset.sub_base _ (by rw [slots_eq, grpSlot_eq] <;> omega)
  · rw [VG.Arm.addr_add (by rw [tailSlot_eq] <;> omega)]
    exact VG.Offset.sub_base _ (by rw [slots_eq, tailSlot_eq] <;> omega)

end VG.Proof.Camellia.Arm
