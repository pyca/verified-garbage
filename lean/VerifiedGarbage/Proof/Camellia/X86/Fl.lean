module

public import VerifiedGarbage.Proof.Camellia.X86.Round
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Camellia.Bitsliced

/-!
# FL and FLINV on x86 (32-bit)

As on ARMv7 (`Proof/Camellia/Arm/Fl.lean`): the two steps of FL (`flRot`,
`flOr`) AND and OR the planes with the subkey's, so they are not linear,
and are run symbolically: one plane's instructions for any plane
(`flRotStep_ok`, `flOrStep_ok`), composed by induction over the planes.
Every plane stays in its slot; each step computes one in `eax`.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Camellia.X86
open VG.Impl.Aes.X86 (sb tmpRegs slotAt movS andS xorS st rorI)

/-! ## Instructions on slots and the table -/

/-- What a write of the register `d` keeps. -/
structure Keeps (s t : State) (d : Reg) : Prop where
  gpr : ∀ r, r ≠ d → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Keeps.trans {s t u : State} {d : Reg} (h₁ : Keeps s t d) (h₂ : Keeps t u d) : Keeps s u d :=
  ⟨fun r h => (h₂.gpr r h).trans (h₁.gpr r h), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Keeps.ok {s t : State} {d : Reg} (h : Keeps s t d) (h1 : d ≠ sb) (h2 : d ≠ kp)
    (hok : Ok layerCfg s) : Ok layerCfg t :=
  hok.congr (h.gpr _ (Ne.symm h1)) (h.gpr _ (Ne.symm h2)) h.rd h.wr

theorem Keeps.slotW {s t : State} {d : Reg} (h : Keeps s t d) (hd : d ≠ sb) (k : Nat) :
    slotW t k = slotW s k := by
  simp only [X86.slotW, h.mem, h.gpr sb (Ne.symm hd)]

theorem Keeps.keyW {s t : State} {d : Reg} (h : Keeps s t d) (hd : d ≠ kp) (k : Nat) :
    keyW t k = keyW s k := by
  simp only [X86.keyW, h.mem, h.gpr kp (Ne.symm hd)]

theorem keeps_setReg (s : State) (d : Reg) (v : BitVec 32) : Keeps s (s.setReg d v) d :=
  ⟨fun _ h => RegUpd.gpr_setReg_of_ne _ _ h, rfl, rfl, rfl⟩

theorem keeps_arith (s : State) (d : Reg) (x v : BitVec 32) (c o : Bool) :
    Keeps s ((arithFlags s x c o).setReg d v) d :=
  ⟨fun _ h => RegUpd.gpr_setReg_of_ne _ _ h, rfl, rfl, rfl⟩

theorem slot_rd {s : State} (hok : Ok layerCfg s) {k : Nat} (hk : k < tailSlot) :
    InRegions (s.rd ++ s.wr) (wordAddr (s.gpr sb) k) 4 := by
  obtain ⟨r, hr, hc⟩ := hok.slotIn k hk
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- One instruction that writes only `d`, with the value it writes. -/
def Step (i : Instr) (u : State) (d : Reg) (v : BitVec 32) : Prop :=
  ∃ t, (∀ is, runBlock isa (i :: is) u = runBlock isa is t) ∧ Keeps u t d ∧ t.gpr d = v

theorem step_ldK {u : State} (hu : Ok layerCfg u) {d : Reg} {w : Nat} (hw : w < 32) :
    Step (ldK d w) u d (keyW u w) := by
  refine ⟨_, fun is => ?_, keeps_setReg u d _, RegUpd.gpr_setReg_self _ _ _⟩
  have h : exec (ldK d w) u = some (u.setReg d (keyW u w)) := by
    have hin : InRegions (u.rd ++ u.wr) (wordAddr (u.gpr kp) w) 4 := hu.extIn w hw
    show (u.load32 (wordAddr (u.gpr kp) w)).map (u.setReg d) = _
    simp only [State.load32, hin, ↓reduceIte, Option.map_some]
  rw [runBlock_cons, h, runStep_some]

theorem step_andS {u : State} (hu : Ok layerCfg u) {d : Reg} {k : Nat} (hk : k < tailSlot) :
    Step (andS d k) u d (u.gpr d &&& slotW u k) := by
  refine ⟨_, fun is => ?_, keeps_arith u d (u.gpr d &&& slotW u k) _ false false, RegUpd.gpr_setReg_self _ _ _⟩
  have h : exec (andS d k) u =
      some ((arithFlags u (u.gpr d &&& slotW u k) false false).setReg d (u.gpr d &&& slotW u k)) := by
    show (u.load32 (wordAddr (u.gpr sb) k)).bind _ = _
    simp only [State.load32, slot_rd hu hk, ↓reduceIte, Option.bind_some]
  rw [runBlock_cons, h, runStep_some]

theorem step_orS {u : State} (hu : Ok layerCfg u) {d : Reg} {k : Nat} (hk : k < tailSlot) :
    Step (orS d k) u d (u.gpr d ||| slotW u k) := by
  refine ⟨_, fun is => ?_, keeps_arith u d (u.gpr d ||| slotW u k) _ false false, RegUpd.gpr_setReg_self _ _ _⟩
  have h : exec (orS d k) u =
      some ((arithFlags u (u.gpr d ||| slotW u k) false false).setReg d (u.gpr d ||| slotW u k)) := by
    show (u.load32 (wordAddr (u.gpr sb) k)).bind _ = _
    simp only [State.load32, slot_rd hu hk, ↓reduceIte, Option.bind_some]
  rw [runBlock_cons, h, runStep_some]

theorem step_xorS {u : State} (hu : Ok layerCfg u) {d : Reg} {k : Nat} (hk : k < tailSlot) :
    Step (xorS d k) u d (u.gpr d ^^^ slotW u k) := by
  refine ⟨_, fun is => ?_, keeps_arith u d (u.gpr d ^^^ slotW u k) _ false false, RegUpd.gpr_setReg_self _ _ _⟩
  have h : exec (xorS d k) u =
      some ((arithFlags u (u.gpr d ^^^ slotW u k) false false).setReg d (u.gpr d ^^^ slotW u k)) := by
    show (u.load32 (wordAddr (u.gpr sb) k)).bind _ = _
    simp only [State.load32, slot_rd hu hk, ↓reduceIte, Option.bind_some]
  rw [runBlock_cons, h, runStep_some]

theorem step_ror8 (u : State) (d : Reg) : Step (rorI d 8) u d ((u.gpr d).rotateRight 8) := by
  refine ⟨(u.setFlags (some ((u.gpr d).rotateRight 8).msb) none u.zf u.sf).setReg d ((u.gpr d).rotateRight 8),
    fun is => ?_, ⟨fun _ h => RegUpd.gpr_setReg_of_ne _ _ h, rfl, rfl, rfl⟩, RegUpd.gpr_setReg_self _ _ _⟩
  have h : exec (rorI d 8) u = some ((u.setFlags (some ((u.gpr d).rotateRight 8).msb) none u.zf u.sf).setReg d
      ((u.gpr d).rotateRight 8)) := by
    simp only [rorI, exec, execShift, Nat.reduceLeDiff, and_self, ↓reduceIte, Nat.reduceEqDiff]
  rw [runBlock_cons, h, runStep_some]

theorem run_st {u : State} (hu : Ok layerCfg u) {r : Reg} {k : Nat} (hk : k < tailSlot) (is : List Instr) :
    runBlock isa (st k r :: is) u =
      runBlock isa is { u with mem := u.mem.writeW (wordAddr (u.gpr sb) k) (u.gpr r) } := by
  have h : exec (st k r) u = some { u with mem := u.mem.writeW (wordAddr (u.gpr sb) k) (u.gpr r) } := by
    have hin : InRegions u.wr (wordAddr (u.gpr sb) k) 4 := hu.slotIn k hk
    show u.store32 (wordAddr (u.gpr sb) k) (u.gpr r) = _
    simp only [State.store32, hin, ↓reduceIte]
  rw [runBlock_cons, h, runStep_some]

theorem ok_setMem {s : State} (h : Ok layerCfg s) (m : Mem) : Ok layerCfg { s with mem := m } :=
  h.congr rfl rfl rfl rfl

/-- A store to slot `k` keeps the other slots below the tail buffer. -/
theorem slot_writeW {s : State} (hok : Ok layerCfg s) {k k' : Nat} (hk : k < tailSlot) (hk' : k' < tailSlot)
    (hne : k' ≠ k) (v : BitVec 32) :
    (s.mem.writeW (wordAddr (s.gpr sb) k) v).readW (wordAddr (s.gpr sb) k') 32 = slotW s k' := by
  have := hok.fit
  simp only [layerCfg, tailSlot] at this hk hk'
  exact Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hne) (by decide)

theorem slot_writeW_self {s : State} (k : Nat) (v : BitVec 32) :
    (s.mem.writeW (wordAddr (s.gpr sb) k) v).readW (wordAddr (s.gpr sb) k) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

/-- A store to slot `k` keeps the table's words at `kp`. -/
theorem key_writeW {s : State} (hok : Ok layerCfg s) {k w : Nat} (hk : k < tailSlot) (hw : w < 32)
    (v : BitVec 32) :
    (s.mem.writeW (wordAddr (s.gpr sb) k) v).readW (wordAddr (s.gpr kp) w) 32 = keyW s w := by
  have h := hok.sep k hk w hw
  exact Mem.readW_writeW_sep (fun x h1 h2 => h x h2 h1) (by decide)

theorem stS_frame {s : State} (hok : Ok layerCfg s) {k : Nat} (hk : k < tailSlot) (v : BitVec 32) :
    Frame [slotRegion layerCfg s] s.mem (s.mem.writeW (wordAddr (s.gpr sb) k) v) := by
  have := hok.fit
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
  simp only [slotRegion, layerCfg]
  exact slot_contains _ hk this

/-- What a step that stores `v` to slot `k` gives. -/
structure StorePost (s s' : State) (k : Nat) (v : BitVec 32) : Prop where
  ok : Ok layerCfg s'
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  slots : ∀ k' < tailSlot, slotW s' k' = if k' = k then v else slotW s k'
  keys : ∀ w < 32, keyW s' w = keyW s w
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [slotRegion layerCfg s] s.mem s'.mem

/-- A store of `eax` to slot `k`, after register writes of `eax`. -/
theorem store_post {s t : State} (hok : Ok layerCfg s) (hk : Keeps s t .eax) {k : Nat} (hkt : k < tailSlot)
    (is : List Instr) :
    ∃ s', runBlock isa (st k .eax :: is) t = runBlock isa is s' ∧ StorePost s s' k (t.gpr .eax) := by
  have okt := hk.ok (by decide) (by decide) hok
  have b : t.gpr sb = s.gpr sb := hk.gpr _ (by decide)
  have p : t.gpr kp = s.gpr kp := hk.gpr _ (by decide)
  refine ⟨_, run_st okt hkt is, ok_setMem okt _, fun r h => hk.gpr r h, fun k' hk' => ?_, fun w hw => ?_,
    hk.rd, hk.wr, ?_⟩
  · show (t.mem.writeW (wordAddr (t.gpr sb) k) (t.gpr .eax)).readW (wordAddr (t.gpr sb) k') 32 = _
    rw [b, hk.mem]
    split
    · rename_i h; subst h; exact slot_writeW_self _ _
    · rename_i h; exact slot_writeW hok hkt hk' h _
  · show (t.mem.writeW (wordAddr (t.gpr sb) k) (t.gpr .eax)).readW (wordAddr (t.gpr kp) w) 32 = _
    rw [b, p, hk.mem]
    exact key_writeW hok hkt hw _
  · show Frame _ s.mem (t.mem.writeW (wordAddr (t.gpr sb) k) (t.gpr .eax))
    rw [b, hk.mem]
    exact stS_frame hok hkt _

/-! ## One plane of each step -/

/-- The rotation step's new right plane `j`: the AND of plane `j - 1` of the
left word and the subkey's, rotated by a byte for plane 0. -/
def rotV (L K : Nat → BitVec 32) (j : Nat) : BitVec 32 :=
  let v := K ((j + 7) % 8) &&& L ((j + 7) % 8)
  if j = 0 then v.rotateRight 8 else v

theorem flRotStep_ok {s : State} (hok : Ok layerCfg s) {d off j : Nat} (hd : d + 16 ≤ tailSlot)
    (hj : j < 8) (hw : off + 8 ≤ 32) :
    ∃ s', runBlock isa (flRotStep d off j) s = some s' ∧
      StorePost s s' (d + 8 + j)
        (slotW s (d + 8 + j) ^^^ rotV (half s d) (fun i => keyW s (off + i)) j) := by
  have hi : (j + 7) % 8 < 8 := Nat.mod_lt _ (by decide)
  obtain ⟨t₁, r₁, k₁, v₁⟩ := step_ldK hok (d := .eax) (w := off + (j + 7) % 8) (by omega)
  have ok₁ := k₁.ok (by decide) (by decide) hok
  obtain ⟨t₂, r₂, k₂, v₂⟩ := step_andS ok₁ (d := .eax) (k := d + (j + 7) % 8) (by omega)
  have k₁₂ := k₁.trans k₂
  -- The rotation, for plane 0.
  have pre : ∃ t, (∀ is, runBlock isa ((if j = 0 then [rorI .eax 8] else []) ++ is) t₂ = runBlock isa is t) ∧
      Keeps s t .eax ∧ t.gpr .eax = rotV (half s d) (fun i => keyW s (off + i)) j := by
    have hv : t₂.gpr .eax = keyW s (off + (j + 7) % 8) &&& slotW s (d + (j + 7) % 8) := by
      rw [v₂, v₁, k₁.slotW (by decide)]
    by_cases h0 : j = 0
    · obtain ⟨t₃, r₃, k₃, v₃⟩ := step_ror8 t₂ .eax
      refine ⟨t₃, fun is => ?_, k₁₂.trans k₃, ?_⟩
      · simp only [h0, ↓reduceIte, List.cons_append, List.nil_append, r₃]
      · rw [v₃, hv]; simp only [rotV, h0, ↓reduceIte, half]
    · refine ⟨t₂, fun is => ?_, k₁₂, ?_⟩
      · simp only [h0, ↓reduceIte, List.nil_append]
      · rw [hv]; simp only [rotV, h0, ↓reduceIte, half]
  obtain ⟨t₃, r₃, k₃, v₃⟩ := pre
  have ok₃ := k₃.ok (by decide) (by decide) hok
  obtain ⟨t₄, r₄, k₄, v₄⟩ := step_xorS ok₃ (d := .eax) (k := d + 8 + j) (by omega)
  obtain ⟨s', r₅, p₅⟩ := store_post hok (k₃.trans k₄) (k := d + 8 + j) (by omega) []
  refine ⟨s', ?_, ?_⟩
  · simp only [flRotStep, List.cons_append, List.nil_append]
    rw [r₁, r₂, r₃, r₄, r₅, runBlock_nil]
  · rw [v₄, v₃, k₃.slotW (by decide), BitVec.xor_comm] at p₅
    exact p₅

theorem flOrStep_ok {s : State} (hok : Ok layerCfg s) {d off j : Nat} (hd : d + 16 ≤ tailSlot)
    (hj : j < 8) (hw : off + 16 ≤ 32) :
    ∃ s', runBlock isa (flOrStep d off j) s = some s' ∧
      StorePost s s' (d + j) (slotW s (d + j) ^^^ (keyW s (off + 8 + j) ||| slotW s (d + 8 + j))) := by
  obtain ⟨t₁, r₁, k₁, v₁⟩ := step_ldK hok (d := .eax) (w := off + 8 + j) (by omega)
  have ok₁ := k₁.ok (by decide) (by decide) hok
  obtain ⟨t₂, r₂, k₂, v₂⟩ := step_orS ok₁ (d := .eax) (k := d + 8 + j) (by omega)
  have ok₂ := k₂.ok (by decide) (by decide) ok₁
  obtain ⟨t₃, r₃, k₃, v₃⟩ := step_xorS ok₂ (d := .eax) (k := d + j) (by omega)
  have k₁₃ := k₁.trans (k₂.trans k₃)
  obtain ⟨s', r₄, p₄⟩ := store_post hok k₁₃ (k := d + j) (by omega) []
  refine ⟨s', ?_, ?_⟩
  · simp only [flOrStep]
    rw [r₁, r₂, r₃, r₄, runBlock_nil]
  · rw [v₃, v₂, v₁, (k₁.trans k₂).slotW (by decide), k₁.slotW (by decide), BitVec.xor_comm] at p₄
    exact p₄

theorem runBlock_range_succ {f : Nat → List Instr} {n : Nat} {s : State} :
    runBlock isa ((List.range (n + 1)).flatMap f) s = (runBlock isa ((List.range n).flatMap f) s).bind
      (runBlock isa (f n)) := by
  rw [List.range_succ, List.flatMap_append, runBlock_app, List.flatMap_singleton]

theorem itePos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a :=
  by simp only [h, ↓reduceIte]

theorem iteNeg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b :=
  by simp only [h, ↓reduceIte]

/-- What a run of steps keeps and changes. -/
structure StepsPost (s s' : State) (f : Nat → Option (BitVec 32)) : Prop where
  ok : Ok layerCfg s'
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  slots : ∀ k < tailSlot, slotW s' k = (f k).getD (slotW s k)
  keys : ∀ w < 32, keyW s' w = keyW s w
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [slotRegion layerCfg s] s.mem s'.mem

/-- The rotation step on the half at slot `d`, plane by plane. -/
theorem flRot_ok {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ tailSlot)
    (hw : off + 8 ≤ 32) : ∀ n ≤ 8,
    ∃ s', runBlock isa ((List.range n).flatMap (flRotStep d off)) s = some s' ∧
      StepsPost s s' fun k => if d + 8 ≤ k ∧ k < d + 8 + n then
        some (slotW s k ^^^ rotV (half s d) (fun i => keyW s (off + i)) (k - (d + 8))) else none
  | 0, _ => ⟨s, runBlock_nil, hok, fun _ _ => rfl,
      fun k _ => by simp only [show ¬ (d + 8 ≤ k ∧ k < d + 8 + 0) by omega, ↓reduceIte, Option.getD_none],
      fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s₁, h₁, p₁⟩ := flRot_ok hok hd hw n (by omega)
    obtain ⟨s₂, h₂, p₂⟩ := flRotStep_ok p₁.ok (d := d) (off := off) (j := n) hd (by omega) hw
    have hrv : rotV (half s₁ d) (fun i => keyW s₁ (off + i)) n =
        rotV (half s d) (fun i => keyW s (off + i)) n := by
      have hi : (n + 7) % 8 < 8 := Nat.mod_lt _ (by decide)
      simp only [rotV, half, p₁.keys _ (show off + (n + 7) % 8 < 32 by omega),
        p₁.slots _ (show d + (n + 7) % 8 < tailSlot by omega),
        iteNeg (show ¬ (d + 8 ≤ d + (n + 7) % 8 ∧ d + (n + 7) % 8 < d + 8 + n) by omega), Option.getD_none]
    refine ⟨s₂, by rw [runBlock_range_succ, h₁, Option.bind_some, h₂], p₂.ok,
      fun r h => (p₂.gpr r h).trans (p₁.gpr r h), fun k hk => ?_,
      fun w hw' => (p₂.keys w hw').trans (p₁.keys w hw'), p₂.rd.trans p₁.rd, p₂.wr.trans p₁.wr, ?_⟩
    · rw [p₂.slots k hk]
      split
      · rename_i h; subst h
        rw [p₁.slots _ hk, iteNeg (by omega), Option.getD_none, hrv, itePos (by omega), Option.getD_some,
          show d + 8 + n - (d + 8) = n by omega]
      · rename_i h
        rw [p₁.slots k hk]
        by_cases h' : d + 8 ≤ k ∧ k < d + 8 + n
        · rw [itePos h', itePos (by omega)]
        · rw [iteNeg h', iteNeg (by omega)]
    · have e : slotRegion layerCfg s₁ = slotRegion layerCfg s := by
        simp only [slotRegion, layerCfg, p₁.gpr sb (by decide)]
      exact p₁.frame.trans (e ▸ p₂.frame)

/-- The OR step on the half at slot `d`, plane by plane. -/
theorem flOr_ok {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ tailSlot)
    (hw : off + 16 ≤ 32) : ∀ n ≤ 8,
    ∃ s', runBlock isa ((List.range n).flatMap (flOrStep d off)) s = some s' ∧
      StepsPost s s' fun k => if d ≤ k ∧ k < d + n then
        some (slotW s k ^^^ (keyW s (off + 8 + (k - d)) ||| slotW s (k + 8))) else none
  | 0, _ => ⟨s, runBlock_nil, hok, fun _ _ => rfl,
      fun k _ => by simp only [show ¬ (d ≤ k ∧ k < d + 0) by omega, ↓reduceIte, Option.getD_none],
      fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | n + 1, hn => by
    obtain ⟨s₁, h₁, p₁⟩ := flOr_ok hok hd hw n (by omega)
    obtain ⟨s₂, h₂, p₂⟩ := flOrStep_ok p₁.ok (d := d) (off := off) (j := n) hd (by omega) hw
    refine ⟨s₂, by rw [runBlock_range_succ, h₁, Option.bind_some, h₂], p₂.ok,
      fun r h => (p₂.gpr r h).trans (p₁.gpr r h), fun k hk => ?_,
      fun w hw' => (p₂.keys w hw').trans (p₁.keys w hw'), p₂.rd.trans p₁.rd, p₂.wr.trans p₁.wr, ?_⟩
    · rw [p₂.slots k hk]
      split
      · rename_i h; subst h
        rw [p₁.slots _ hk, p₁.slots _ (show d + 8 + n < tailSlot by omega), p₁.keys _ (by omega),
          iteNeg (by omega), iteNeg (by omega), Option.getD_none, Option.getD_none, itePos (by omega),
          Option.getD_some, show d + n - d = n by omega, show d + n + 8 = d + 8 + n by omega]
      · rename_i h
        rw [p₁.slots k hk]
        by_cases h' : d ≤ k ∧ k < d + n
        · rw [itePos h', itePos (by omega)]
        · rw [iteNeg h', iteNeg (by omega)]
    · have e : slotRegion layerCfg s₁ = slotRegion layerCfg s := by
        simp only [slotRegion, layerCfg, p₁.gpr sb (by decide)]
      exact p₁.frame.trans (e ▸ p₂.frame)

theorem getLsbD_ror8 (x : BitVec 32) {p : Nat} (hp : p < 32) :
    (x.rotateRight 8).getLsbD p = x.getLsbD ((p + 8) % 32) := by
  rw [BitVec.getLsbD_rotateRight]
  split
  · congr 1; omega
  · rename_i h; simp only [Nat.reduceMod, Nat.not_lt] at h; simp only [hp, decide_true, Bool.true_and]
    congr 1; omega

theorem rotV_bit {L K : Nat → BitVec 32} {j p : Nat} (hp : p < 32) :
    (rotV L K j).getLsbD p =
      ((L ((j + 7) % 8)).getLsbD (W32.rotPos j p) && (K ((j + 7) % 8)).getLsbD (W32.rotPos j p)) := by
  simp only [rotV, W32.rotPos]
  split
  · rw [getLsbD_ror8 _ hp, BitVec.getLsbD_and, Bool.and_comm]
  · rw [BitVec.getLsbD_and, Bool.and_comm]

/-- The rotation step, as `W32.RotStep`. -/
theorem flRot_step {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ tailSlot)
    (hw : off + 8 ≤ 32) :
    ∃ s', runBlock isa (flRot d off) s = some s' ∧
      W32.RotStep (half s d) (fun i => keyW s (off + i)) (half s' d) ∧
      StepsPost s s' fun k => if d + 8 ≤ k ∧ k < d + 16 then some (slotW s' k) else none := by
  obtain ⟨s', h, p⟩ := flRot_ok hok hd hw 8 (Nat.le_refl _)
  refine ⟨s', h, ⟨fun j hj => ?_, fun j hj p' hp => ?_⟩, ⟨p.ok, p.gpr, fun k hk => ?_, p.keys, p.rd, p.wr,
    p.frame⟩⟩
  · simp only [half]; rw [p.slots _ (by omega), iteNeg (by omega), Option.getD_none]
  · simp only [half]
    rw [p.slots _ (by omega), itePos (by omega), Option.getD_some, BitVec.getLsbD_xor, rotV_bit hp,
      show d + (8 + j) - (d + 8) = j by omega]
    rfl
  · split
    · rfl
    · rw [p.slots k hk, iteNeg (by omega), Option.getD_none]

/-- The OR step, as `W32.OrStep`. -/
theorem flOr_step {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ tailSlot)
    (hw : off + 16 ≤ 32) :
    ∃ s', runBlock isa (flOr d off) s = some s' ∧
      W32.OrStep (half s d) (fun i => keyW s (off + i)) (half s' d) ∧
      StepsPost s s' fun k => if d ≤ k ∧ k < d + 8 then some (slotW s' k) else none := by
  obtain ⟨s', h, p⟩ := flOr_ok hok hd hw 8 (Nat.le_refl _)
  refine ⟨s', h, ⟨fun j hj => ?_, fun j hj p' hp => ?_⟩, ⟨p.ok, p.gpr, fun k hk => ?_, p.keys, p.rd, p.wr,
    p.frame⟩⟩
  · simp only [half]; rw [p.slots _ (by omega), iteNeg (by omega), Option.getD_none]
  · simp only [half]
    rw [p.slots _ (by omega), itePos (by omega), Option.getD_some, BitVec.getLsbD_xor, BitVec.getLsbD_or,
      Bool.or_comm, show d + j - d = j by omega, show d + j + 8 = d + (8 + j) by omega,
      show off + 8 + j = off + (8 + j) by omega]
  · split
    · rfl
    · rw [p.slots k hk, iteNeg (by omega), Option.getD_none]

/-- What FL and FLINV keep and change. -/
structure FlPost (s s' : State) (d : Nat) : Prop where
  ok : Ok layerCfg s'
  slots : ∀ k < tailSlot, (k < d ∨ d + 16 ≤ k) → slotW s' k = slotW s k
  keys : ∀ w < 32, keyW s' w = keyW s w
  gpr : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [slotRegion layerCfg s] s.mem s'.mem

theorem StepsPost.slot_out {s s' : State} {lo hi : Nat}
    (p : StepsPost s s' fun k => if lo ≤ k ∧ k < hi then some (slotW s' k) else none)
    {k : Nat} (hk : k < tailSlot) (h : k < lo ∨ hi ≤ k) : slotW s' k = slotW s k := by
  rw [p.slots k hk, iteNeg (by omega), Option.getD_none]

theorem flPost_trans {s s₁ s₂ : State} {d : Nat} {lo₁ hi₁ lo₂ hi₂ : Nat}
    (p₁ : StepsPost s s₁ fun k => if lo₁ ≤ k ∧ k < hi₁ then some (slotW s₁ k) else none)
    (p₂ : StepsPost s₁ s₂ fun k => if lo₂ ≤ k ∧ k < hi₂ then some (slotW s₂ k) else none)
    (h₁ : d ≤ lo₁ ∧ hi₁ ≤ d + 16) (h₂ : d ≤ lo₂ ∧ hi₂ ≤ d + 16) : FlPost s s₂ d where
  ok := p₂.ok
  slots k hk h := by rw [p₂.slot_out hk (by omega), p₁.slot_out hk (by omega)]
  keys w hw := (p₂.keys w hw).trans (p₁.keys w hw)
  gpr r h := (p₂.gpr r h).trans (p₁.gpr r h)
  rd := p₂.rd.trans p₁.rd
  wr := p₂.wr.trans p₁.wr
  frame := by
    have e : slotRegion layerCfg s₁ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg, p₁.gpr sb (by decide)]
    exact p₁.frame.trans (e ▸ p₂.frame)

theorem fl_ok {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ tailSlot) (hw : off + 16 ≤ 32)
    {x : Nat → BitVec 64} {k : BitVec 64} (hQ : W32.HalfRel (half s d) x)
    (hK : W32.HalfRel (fun i => keyW s (off + i)) fun _ => k) :
    ∃ s', runBlock isa (flCode d off) s = some s' ∧
      W32.HalfRel (half s' d) (fun b => Spec.Camellia.fl (x b) k) ∧ FlPost s s' d := by
  obtain ⟨s₁, h₁, r₁, p₁⟩ := flRot_step hok hd (off := off) (by omega)
  obtain ⟨s₂, h₂, r₂, p₂⟩ := flOr_step p₁.ok hd hw
  have hr := W32.fl_rel hQ hK r₁ ⟨r₂.1, fun j hj p hp => by
    rw [r₂.2 j hj p hp]; dsimp only; rw [p₁.keys _ (by omega)]⟩
  refine ⟨s₂, ?_, hr, flPost_trans p₁ p₂ (by omega) (by omega)⟩
  rw [flCode, runBlock_app, h₁, Option.bind_some, h₂]

theorem flinv_ok {s : State} (hok : Ok layerCfg s) {d off : Nat} (hd : d + 16 ≤ tailSlot) (hw : off + 16 ≤ 32)
    {x : Nat → BitVec 64} {k : BitVec 64} (hQ : W32.HalfRel (half s d) x)
    (hK : W32.HalfRel (fun i => keyW s (off + i)) fun _ => k) :
    ∃ s', runBlock isa (flinvCode d off) s = some s' ∧
      W32.HalfRel (half s' d) (fun b => Spec.Camellia.flinv (x b) k) ∧ FlPost s s' d := by
  obtain ⟨s₁, h₁, r₁, p₁⟩ := flOr_step hok hd hw
  obtain ⟨s₂, h₂, r₂, p₂⟩ := flRot_step p₁.ok hd (off := off) (by omega)
  have hr := W32.flinv_rel hQ hK r₁ ⟨r₂.1, fun j hj p hp => by
    have hi : (j + 7) % 8 < 8 := Nat.mod_lt _ (by decide)
    rw [r₂.2 j hj p hp]; dsimp only; rw [p₁.keys _ (by omega)]⟩
  refine ⟨s₂, ?_, hr, flPost_trans p₁ p₂ (by omega) (by omega)⟩
  rw [flinvCode, runBlock_app, h₁, Option.bind_some, h₂]

end VG.Proof.Camellia.X86
